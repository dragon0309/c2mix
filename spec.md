# c2mix：C → SMT2（CryptoLine mix 格式）轉換器規格

- 文件狀態：草案 v0.5，2026-09-24（v0.1 用 CBMC 前端；v0.2 改為 LLVM 前端，見 D1；v0.3 為審查後的修正；
  v0.4 為第 3 階段的實測結果：LF1–LF4 轉為已實測、§6.4 新增 H5/H6、§9 加上第 3 階段結論、新增 §10.3 工作規則；
  v0.5 為第 4 階段進行中的實測：§6.3 複製沿用 atom、§6.4 判定的實作、§7.4 range VC 拆分與 G5 的多查詢規則、
  §4.1 新鍵、§9 第 4 階段進度與兩個待決問題）
- 專案型態：獨立專案。輸出的消費端是 extend_z3 `bin/main`（`main` @ `56bd0cb`），視為外部依賴
- 工具鏈基準：
  - 主前端：clang / LLVM 18（Ubuntu 24.04 的 apt 預設版本；LF1–LF4 已於 A3.0 實測，見 §2.0）
  - oracle：Z3 4.8.12（CLI）、Python 3.12.3
  - 第二前端（選配，第 6 階段）：CBMC 6.11.0

本文中 `extend_z3/…` 指 extend_z3 repo 裡的路徑。

## 0. 摘要

**目的：產生給 extend_z3 跑的例子。** extend_z3 目前確認正確的輸入只有兩組 golden，都是 CryptoLine
從組語產生的（§2.1）。c2mix 從 C 程式產生同格式的 VC，讓 extend_z3 有更多例子可以跑。所以
c2mix 產生的 VC 若 extend_z3 解不出來，這本身也是關於 extend_z3 的結果，不只是轉換器的問題（R6）。

c2mix 把「C 函式 + 規格」轉成 extend_z3 可以直接求解的驗證條件（VC）：每個 cut 一個
五段式 `.smt2`，格式與 CryptoLine `cv -save-mix` 相同（例如
`extend_z3/input/pqclean_kyber768_avx2_noAssume/`）。

前端流程：clang 把 C 編成 LLVM IR，c2mix 用自己的執行器走過這份 IR。走的時候控制流用具體值，
資料保持符號化，所以迴圈會被完全展開、陣列元素會變成各自的 SSA 值。c2mix **不依賴 LLVM
的最佳化 pass** 做展開或純量化。

**核心不含任何密碼學方案的知識。** 方案相關的內容全部放在 `targets/<name>/` 的規格模組：
要驗哪個函式、輸入怎麼解讀成整數或多項式、要證的同餘式、cut 放在哪裡。核心只認得
C 的整數語意和一組通用的代數編碼規則。

通用性有兩道檢查。第一道是 G10：核心程式碼裡不准出現方案名稱或方案常數。第二道是
第 5 階段的 held-out 驗收：拿開發期間完全沒碰過的 5 個演算法，只寫規格、不改核心，
就要跑通全部驗證關卡。

每個階段都有獨立的驗收項目與出口條件，前一階段沒通過，下一階段不開始。

**正確性依據只有兩組 golden**：`extend_z3/input/pqclean_kyber768_avx2_noAssume/` 與
`extend_z3/input/openssl/ecp_nistz256/x86_64/`（§2.1）。其他語料只拿來當測試輸入或參考。

---

## 1. 目標與範圍

### 1.1 目標

1. 輸入是一組 C 原始檔加一個規格模組。上游原始碼不修改，cut 標記用 patch 插入。
2. 對每個 cut 產生兩個檔案：
   - `cutN.smt2`：五段式 mix VC，給 `bin/main` 求解。
   - `cutN.range.smt2`：純 `QF_BV` 的範圍、安全與 hint 義務，給 `z3` 求解。
3. 另外產生 `manifest.json`，記錄符號對照、每個決策與統計數字。
4. 所有 VC 都是 `unsat` ⇒ 程式對滿足前置條件的輸入滿足後置條件（§8.2）。

### 1.2 支援的 C 子集（v1）

| 面向 | v1 支援 | v1 明確拒絕（附錯誤碼） |
|---|---|---|
| 整數型別 | `int8_t`…`int64_t`、`uint8_t`…`uint64_t`、`__int128`、`unsigned __int128`、`int`/`long` 等（LP64） | 浮點、bit-field、`_BitInt` |
| 運算 | `+ - *`、常數位移、轉型、`& \| ^ ~`、比較、`?:` | 除法與取餘 `E-DIV`（v2）、變數位移量 `E-VAR-SHIFT` |
| 資料 | 純量、定長陣列（含多維）、以陣列為參數、struct 內的定長陣列（以指標傳遞）、`const` 常數表 | heap、非常數位址 `E-DYN-INDEX`、以不同型別存取同一塊記憶體 `E-MIXED-ACCESS`、讀取未初始化的記憶體 `E-UNINIT`、以值傳遞或回傳 struct `E-UNSUPPORTED`、參數互相 alias |
| 控制流 | 條件只依賴常數的分支與迴圈（執行器直接走，等於完全展開）；函式呼叫（inline）；條件依賴輸入、而且能在後支配點合流的 `if/else` 與 `?:`（合流成 `select`，由 L12 處理） | 條件依賴輸入的迴圈 `E-SYMBOLIC-LOOP`、無法合流的輸入相依分支 `E-SYMBOLIC-BRANCH`、遞迴或超過步數上限 `E-UNBOUNDED` |
| 其他 | — | SIMD 向量型別 `E-VECTOR`（第 6 階段）、x86 intrinsics `E-INTRINSIC`、未定義的外部函式 `E-EXTERNAL-CALL`、`volatile`、I/O、多執行緒 |

### 1.3 支援的規格（v1）

- **解讀（interpretation）**：
  - 單一整數。
  - 多 limb 整數 Σ lᵢ·2^(b·i)，飽和或非飽和的 radix 都可以。
  - 多項式 Σ cᵢ·xⁱ。
  - 使用者在 DSL 裡自訂的算式。
- **斷言**：
  - 範圍：`lo ≤ v < hi`，有號或無號。
  - `eq`：整數或多項式恆等。
  - `eqmod`：模數可以是常數、多項式或程式變數。
- **求解器限制**：extend_z3 只有 `eqmodP1`/`eqmodP2` 有編譯後的處理（`eqmodP3`/`eqmodP4` 只有宣告），
  所以一個 `eqmod` 最多 2 個模數。超過時規格自檢 S2 直接報錯，不自動拆分。

### 1.4 非目標

- 一般性 C 程式驗證（記憶體安全、UB 偵測）。
- 產生 CryptoLine `.cl`。
- 驗證 extend_z3、Z3 或 clang 的正確性，三者列為信任基礎。
- v1 不處理 SIMD、GF(2)[x] 代數、除法（見第 6 階段）。

---

## 2. 設計依據

### 2.0 事實清單

「已實測」表示撰寫本規格時實際跑過，重現指令見附錄 C。「待實測」是根據 LLVM 文件的預期，
必須在 A3.0 實測確認，確認之前不得當作已知事實使用。

| # | 狀態 | 事實 | 影響 |
|---|---|---|---|
| F1 | 已實測 | 五段式格式就是 CryptoLine `cv -save-mix` 的輸出；兩組 golden（§2.1）都是這個格式，五行 section 註解逐字相同 | 輸出格式有現成的參考實作 |
| F2 | 已實測 | `extend_z3/src/smt2_frontend.cpp` 會把 `Poly` datatype 和 `eqP`/`eqmodP1..4` 的 prelude 插在 `(set-logic` 那行之後。只要檔案自己宣告了 `Poly`，就整個不注入 | 輸出契約 M1、M2 |
| F3 | 已實測 | Z3 4.8.12 把 `bv2int` 當無號：`(simplify (bv2int #xFFFF))` 得 65535。把 golden 的乘法橋接式代入 f = −1：Z3 讀法下為**假**，有號讀法下為真。既有修正是 `extend_z3/working/cbmc_small/signed_alias.py` | 有號值必須用 alias 編碼（D4） |
| F5 | 已實測 | Kyber ref `ntt()` 的模數樹和 `pqclean_kyber768_avx2_noAssume` 全部 cut 的後置條件，七層逐層**集合相等**（2、4、…、128 個模數） | 數學層 golden 比對（A4.2） |
| F6 | 已實測 | 基準（`extend_z3/shs/benchmark_results.md`，2026-08-23）：Kyber noAssume 15 檔共 185.19 s（需 partition prepass）；OpenSSL 9 檔共 4.49 s（不需 partition prepass）。flag 組合見 `extend_z3/shs/regression_76.sh` | 效能比較基準 |
| F7 | 已實測 | `extend_z3/working/cbmc_small/` 有 4 個程式，每個都附 C 版、手寫 `.cl`、`cv` 產生的 `mix_0.smt2`。Montgomery 的 `.cl` 用 `assert true && lo = 0; assume lo = 0 && true;` 把 range 事實轉進代數層 | hint 機制的原型（§6.4）。這組**未確認正確**：只拿它的 C 原始碼當測試輸入 |
| F10 | 已實測（2026-09-23） | `bin/main` 的 `sat` **不代表 VC 是假的**，只代表沒有證出來：同一個 T2b 的 `cut0.smt2`，不加 partition prepass 是 `sat`（128 s），加了之後 0.24 s `unsat`。真的假 VC（把 T2c 的模數改成 q+1）兩種 flag 都是 `sat` | G6 只認 `unsat`；遇到 `sat` 要先用 G3/G4 分類（R6）。c2mix 自己的輸出預設帶 prepass flag |
| F9 | 已實測（2026-09-23） | z3 4.8.12 對「BV 加 Int 非線性」的混合式很弱：附錄 A 的 L4′ 16-bit 引理逾時（> 120 s），L3 加法 8/16-bit 也逾時（> 25 s）；同一批規則在 w = 4 全部 `unsat`（約 1 s）。改寫成純 QF_BV 的像之後，w ≤ 32 全部秒解，只有 64/128-bit 乘法仍逾時 | A1.1 的做法（見第 1 階段）與附錄 A |
| F8 | 已實測 | Ubuntu 24.04 的 apt 候選版本：`clang`/`llvm` 為 18，另有 `clang-19`、`clang-20`；`cbmc` 為 6.11.0 | 工具鏈可以用 apt 安裝並鎖版本 |
| F4 | 已實測（CBMC） | CBMC 6.11 的行為：陣列要加 `--max-field-sensitivity-array-size 256` 才會展開成純量；元素名是大寫十六進位；常數表會被摺疊；`unsigned __int128` 可用（`fiat_p256_mul` 產生 168 處 `BitVec 128`、0 個 guard） | 只用於第二前端（第 6 階段）。細節見附錄 E |
| LF1 | 已實測（2026-09-23） | clang 在 `-O0` 下會替函式加 `optnone`，之後 `opt` 的 pass 都不作用；加 `-Xclang -disable-O0-optnone` 才能跑 `mem2reg`。實測：不加旗標時 `mem2reg` 之後仍有 8 個 `alloca`，加了之後 0 個 | 前端旗標（§5.3） |
| LF2 | 已實測（2026-09-23） | 加 `-fwrapv` 後，`-O0` 加 `mem2reg` 產生的 IR 不含任何會產生 poison 的旗標（`nsw`、`nuw`、`exact`、`nneg`、`disjoint` 等）。實測：同一支程式不加 `-fwrapv` 有 7 處，加了之後 0 處；第 3 階段 14 個目標的 IR 合計 0 處 | 執行器遇到這類旗標就拒絕（`E-POISON-FLAG`），不必模擬 poison 語意 |
| LF3 | 已實測（2026-09-23） | `const` 常數表的讀取是對 `@zetas` 這種 `constant` 全域的 GEP 加 load，索引在展開後是常數 | 執行器直接摺疊 |
| LF4 | 已實測（2026-09-23） | `unsigned __int128` 對應到 `i128` 運算；fiat-crypto `p256_64.c` 的 IR 落在 §5.4 的支援子集內（用到的指令：add、alloca、and、call、load、lshr、ret、store、trunc、zext）。**前提**：要定義 `FIAT_P256_NO_ASM`，否則 `fiat_p256_value_barrier_u64` 是 `asm` 敘述，不在子集內；這個 `#define` 寫在產生的 harness 裡，不是編譯旗標（§5.3 的旗標仍然固定） | 多 limb 目標可行 |
| LF5 | 待實測 | `_mm256_add_epi16` 會變成 `add <16 x i16>`，`_mm256_mulhi_epi16` 會變成 `@llvm.x86.avx2.pmulh.w` | 第 6 階段的 SIMD 支援 |

### 2.1 golden 語料

只有下面兩組確認正確，所有「和 golden 比對」的驗收都只用這兩組：

| 目錄（在 `extend_z3/input/` 下） | 檔數 | 來源 | 型別 | 代數 | 基準（F6） |
|---|---:|---|---|---|---|
| `pqclean_kyber768_avx2_noAssume` | 15 | CryptoLine（Kyber AVX2 組語），無 hint | 16-bit 有號（`bv2int`） | 多項式，`eqmodP2`（q, x^k − ζ） | 185.19 s，需 partition prepass |
| `openssl/ecp_nistz256/x86_64` | 9 | CryptoLine（OpenSSL P-256 x86-64 組語） | 64-bit 無號（只有 `bv2nat`） | 4-limb 整數，`eqmodP1` | 4.49 s |

兩組剛好互補：一組是有號、多項式、2 個模數；另一組是無號、多 limb 整數、1 個模數。
兩組合起來涵蓋 extend_z3 目前會處理的兩種同餘判斷式（`eqmodP1`、`eqmodP2`），以及有號和無號兩種整數編碼。

其他語料（`input/pqclean/kyber768/avx2`、`input/saber/*`、`input/simple`、`input/others/redc`、
`working/cbmc_small`、`working/by_divstep`）**未確認正確**。它們可以拿來當 lint 的參考輸入，
或當 C 測試程式的來源，但不能作為任何驗收關卡的預期結果。

兩組 golden 都是從組語產生的，c2mix 的輸入是 C，所以不存在「同一支程式」的逐檔比對，
比對一律在數學層進行（§8.3）。

---

## 3. 架構

```
targets/<t>/spec.py ───────┐
vendor/*.c + cuts.patch ───┤
                           ▼
 [H] harness 產生器 ─────────► harness.c（呼叫 runtime API，§4.2）
                           ▼
 [C] clang-18 + opt-18 ──────► program.ll（-O0、mem2reg，§5.3）
                           ▼
 [P] IR 解析器（支援子集）───► 函式、基本區塊、指令
                           ▼
 [X] 執行器 ────────────────► c2mix IR 軌跡（SSA、純量、無分支）◄── [G2] 與原生執行比對
                           ▼
 [A] 區間分析 / exactness 判定
                           ▼
 [W] lowering（range + algebraic + witness + alias）
                           ▼
 [V] VC 組裝（切段、事實攜帶、hint）
                           ▼
 [E] emit ──► out/<t>/cutN.smt2 · cutN.range.smt2 · manifest.json
```

[C]、[P]、[X] 合稱**前端**。前端的輸出是 c2mix IR 軌跡，這是前端與後段之間唯一的介面。
第 6 階段的 CBMC 第二前端也輸出同一種軌跡。

| 元件 | 輸入 → 輸出 | 職責 | 由誰驗證 |
|---|---|---|---|
| H | spec → `harness.c` | 宣告並登記輸入輸出物件、呼叫目標函式、結束時呼叫 `c2mix_done()` | G2 |
| C | C → `.ll` | 呼叫 clang 與 opt，旗標固定在核心裡，不開放給 target 修改 | A3.0、G2 |
| P | `.ll` → 指令結構 | 只解析支援子集，遇到其他東西就拒絕 | A3.2（round-trip） |
| X | 指令結構 → 軌跡 | 具體控制流、符號資料、記憶體、inline、合流 | G2、A3.7 |
| A | IR → 區間 | 從規格的範圍前提做區間分析，決定每個運算用 EXACT 還是 SPLIT | A1.4、G5 |
| W | IR → 兩套敘述 | 規則 L1–L14（§6） | A1.1–A1.3、G3 |
| V | 敘述 + spec → VC | cut 切段、事實攜帶、hint 發現 | G5、G6、G9 |
| E | VC → 檔案 | 格式契約 M1–M10 | G1、G8 |

### 3.1 決策紀錄

| # | 決策 | 理由 |
|---|---|---|
| D1 | 主前端用 **LLVM IR 加上自己的執行器**。不用 LLVM 的最佳化做展開；CBMC 降為選配的第二前端 | 見下方說明 |
| D2 | Python 3.12，只用標準函式庫；LLVM IR 用**自寫的子集解析器**讀文字格式，並鎖定 LLVM 18；oracle 一律呼叫 CLI（`clang-18`、`z3`、`bin/main`） | llvmlite 綁的是它自己內建的 LLVM 版本，和 clang-18 產生的文字 IR 不一定相容。子集解析器的正確性用 round-trip 驗證（A3.2） |
| D3 | 規格用**內嵌在 Python 的 DSL** | 模數樹、zeta 表、limb 權重都要用程式產生，不另外設計語法與 parser |
| D4 | 有號值預設用 **alias 編碼**（`s__v`）；`--int-encoding=bv2int` 只拿來和 golden 做 A/B | F3。**A0.4（2026-09-22）結論：維持。** Kyber noAssume 15 檔轉成 alias 後全部 `unsat`，合計 130.05 s；同一個 bin/main 跑原檔（bv2int）184.90 s（F6 為 185.19 s）。MaxRSS 峰值 0.83 GB，bv2int 為 2.33 GB。逐檔有快有慢：cut2–6、cut8 快 2.2–3.3 倍，cut0、cut1、cut9–13 慢 1.2–1.7 倍（cut7、cut14 兩種都在 1 s 內）。量測用的是 `signed_alias.py` 的放置方式（alias 定義集中在 declaration 段），與 §6.1 的放置方式不同，第 2 階段要重測（`reports/a0.4-2026-09-22.md`） |
| D5 | 多項式不定元一律 `(PVar "x")` | 宣告成 `(_ BitVec 1)` 的話，整數讀法下模數理想會退化成 (1)（前次分析：504 組全部 gcd = 1） |
| D6 | **exactness 自動判定**：區間分析能證明不溢位 → 精確等式，並把 safety 義務寫進 range VC；證不出來 → SPLIT 編碼 | 不需要逐點標註；兩種結果都 sound |
| D7 | cut 標記 = 呼叫外部函式 `c2mix_cut(tag)`，以 patch 插入 | 在 IR 裡是有順序的 call，順序由構造保證；上游原始碼保持原樣 |
| D8 | ghost 預設用**直接綁定** `(eqP g <多項式>)`。A0.4 若顯示 `bin/main` 無法處理，改用**內嵌**：不產生 ghost 符號，把多項式直接代入每個斷言。golden 的 `(eqP (PPow g 2) …)` 只保留為 `--ghost=legacy-pow2` 供 A/B，不得用在要通過關卡的輸出 | 依 §8.0 的語意，`g² = Σ fᵢxⁱ` 對大多數輸入沒有多項式解 g，前提因此矛盾，VC 會 vacuous 地 `unsat`，G3 也必然失敗。extend_z3 目前能證 golden，是因為它把 g 當成環裡的新變數做理想運算，並不代表這條斷言在語意上可滿足。直接綁定與內嵌都沒有這個問題。**A0.4（2026-09-22）結論：維持直接綁定。** Kyber cut0（ghost 在此綁定）與 cut1（ghost 只在前提與目標）上，三種形式在 alias 與 bv2int 下都是 `unsat`。直接綁定與 legacy-pow2 耗時相同（alias：cut0 15.8 s、cut1 7.9 s）；內嵌在 cut0 相同，在 cut1 慢約 2 倍（16.6 s，因為要多宣告 256 個 entry 值）。鑑別力檢查：把 cut1 目標的一個模數常數加 1 後，三種形式在 300 s 內都沒有得到 `unsat`（逾時，不是 `sat`，只能算弱證據；前提是否可滿足由 G3 負責）（`reports/a0.4-2026-09-22.md`） |

**D1 的說明**

選 LLVM 而不是 CBMC 的理由：

| 面向 | LLVM | CBMC |
|---|---|---|
| 輸入介面 | LLVM IR 有正式的 Language Reference，鎖定大版本後格式穩定 | 讀的是 `--smt2` 的文字輸出，名稱編碼（`!0@1#2[[A0]]`）是內部格式，沒有保證不變 |
| SIMD（第 6 階段） | 直接表達成向量型別與 x86 intrinsic（LF5） | 看不懂 intrinsics，要另外寫 C 模型 |
| 錯誤訊息 | 加 `-g` 後每條指令都帶原始碼行號 | SMT2 輸出沒有行號 |
| cut 標記 | 外部函式呼叫，順序由構造保證 | 靠觀察到的輸出順序（附錄 E） |
| 差分測試 | 原生執行檔用同一個 clang 編，C 語意解讀一致 | CBMC 與編譯器是兩套 C 語意實作 |
| 普及度 | clang 幾乎到處都有 | 要另外安裝特定版本 |

不用 LLVM 的最佳化來展開迴圈，是因為：

- `loop-unroll-full` 受門檻限制，不保證展開完。例如 Kyber `ntt` 的內層迴圈起點
  `start = j + len` 依賴上一層迴圈的結束值，要靠 SCEV 才算得出迭代次數。
- 最佳化會改掉程式形狀（向量化、strength reduction、分支改成 `select`、用 `nsw` 做 UB 推理），
  lowering 規則要處理的形式會跟著變多。

改由 c2mix 自己的執行器負責：條件是常數的分支直接走，所以迴圈自然會被完全展開；
位址是常數的 load/store 直接對應到陣列元素的 SSA 版本。代價是要多寫一個執行器，
但對「控制流只依賴常數」的密碼學核心來說，這個執行器很小。

---

## 4. 輸入

### 4.1 目標目錄

```
targets/<name>/
  target.toml    上游來源（URL + commit）、檔案清單、入口函式、預期結果
  cuts.patch     插入 c2mix_cut(tag) 的 patch（可為空）
  cuts.*.patch   其他 cut 顆粒度的變體（選用），由 target.toml 的 variant 選擇
  spec.py        規格模組
  params.py      方案常數（只能出現在 targets/ 底下，G10）
```

`target.toml` 範例：

```toml
[source]
url    = "https://github.com/pq-crystals/kyber"
commit = "<vendoring 時填入>"
files  = ["ref/ntt.c", "ref/reduce.c"]
entry  = "ntt"

[build]
mode = "include"    # include：harness 直接 #include 上游 .c，可以呼叫 static 函式
                    # link：各檔分別編譯後以 llvm-link 連結
range_split = 16    # 選用：range VC 預設拆成幾個檔（§7.4），--range-split 覆寫

[variants]
half = "cuts.half.patch"      # 選用：c2mix build --variant half

[limits]
max_steps = 100_000_000       # 執行器步數上限，超過就 E-UNBOUNDED

[expect]
must_pass  = true             # G6 必須 unsat（見 §11 R6）
hints_omit = "record"         # noAssume 模式只記錄結果，不作為關卡
phase      = 4                # 哪個階段的驗收負責這個目標（省略時為 3）
```

cut 的位置隨 variant 改變，cut 斷言也要跟著變：`spec.py` 的 `build()` 若接受 `variant` 參數，
核心就把 variant 名稱傳進去（例如 Kyber `ntt` 的 `half`）。

clang 與 opt 的旗標固定在核心裡（§5.3），target 不能改。這樣所有目標走的是同一條前端管線。

`mode` 的預設是 `include`。Kyber 的 `fqmul` 與 fiat-crypto 的原語（`fiat_p256_addcarryx_u64` 等）
都是 `static` 函式，只有在同一個編譯單元裡才呼叫得到。

### 4.2 runtime API 與 cut 標記

`include/c2mix.h`：

```c
#include <stddef.h>
/* 登記一個物件，讓規格可以用 name 引用它 */
void c2mix_register(const char *name, void *p, size_t count, size_t elem_size, int is_signed);
void c2mix_input(const char *name);   /* 把已登記的物件標成符號輸入 */
void c2mix_cut(int tag);              /* cut 標記 */
void c2mix_done(void);                /* 程式結束點（exit 時間點） */
```

同一組 API 有兩種實作：

| 情境 | 實作 |
|---|---|
| c2mix 執行器 | 依函式名攔截這四個呼叫，不需要函式本體 |
| 原生執行（G2） | `runtime/c2mix_rt.c`：`c2mix_input` 從測試向量檔讀值；`c2mix_cut` 與 `c2mix_done` 把所有已登記物件 dump 出來 |

harness 範例（由 H 依規格產生）：

```c
#include <stdint.h>
#include "c2mix.h"
void ntt(int16_t r[256]);
int main(void) {
  int16_t r[256];
  c2mix_register("r", r, 256, sizeof r[0], 1);
  c2mix_input("r");
  ntt(r);
  c2mix_done();
  return 0;
}
```

- **cut 的身分**是 `(tag, k)`，意思是第 k 次執行到帶這個 tag 的 `c2mix_cut`。
- **cut 斷言只能引用已登記的物件**。v1 不支援引用函式內的區域變數。
- **回傳值**：harness 把回傳值存進區域變數後再登記，例如
  `int16_t ret = f(a); c2mix_register("ret", &ret, 1, sizeof ret, 1);`。
- **測試向量格式**（原生執行）：每行一個 JSON 物件，鍵是登記名，值是整數陣列，例如
  `{"r": [12, -7, …]}`。dump 的格式相同，另外帶 `"tag"` 與 `"k"` 兩個鍵（exit 時 tag 為 `"exit"`）。

### 4.3 規格 DSL

**概念**

| 構件 | 說明 |
|---|---|
| `Target(entry, args, returns)` | 參數：`In(Array("int16_t", 256))`、`InOut(...)`、`Out(...)`、`In("int32_t")` |
| `t.arg("r")[i]` | 對已登記物件的參照 |
| `.entry` / `.at(cut)` / `.exit` | 時間點 |
| `Indet("x")` | 多項式不定元 |
| `poly(refs, x)`、`limbs(refs, bits)` | 解讀 |
| `rng(lo <= e < hi)`、`abs_lt(e, b)` | 範圍斷言 → range 段 |
| `eq(a, b)`、`eqmod(a, b, [m1, m2])` | 代數斷言 → algebraic 段 |
| `t.ghost(name, expr)` | 只能引用 entry 值，綁定一次 |
| `t.pre(...)`、`t.cut(tag, k, ...)`、`t.post(...)` | 前置條件、cut 斷言、後置條件 |

**語意規則**

- 同一個斷言不能同時含 range 與 algebraic 部分。
- Int 常數沒有寬度限制。
- 參照的解讀依登記時的 `is_signed`，可以用 `signed()`/`unsigned()` 覆寫。
- hint 由核心自動發現（§6.4）。`t.hint()` 只是逃生口，每次使用都會記在 manifest。

**通用函式庫**（放在 `c2mix/lib/`，不含任何方案常數）

| 模組 | 內容 |
|---|---|
| `lib.poly` | 多項式解讀 |
| `lib.limbs` | 多 limb 整數解讀 |
| `lib.mont` | Montgomery 參數（R、R⁻¹ mod q） |
| `lib.ntt.ct_schedule(n, q, zetas, R, layers)` | Cooley–Tukey 每層的區塊清單 `(lo, hi, deg, ζ)`，涵蓋不完全分解（Kyber）與完全分解（Dilithium）。`zetas` 依程式實際使用的順序給（Kyber ref 從 `zetas[1]` 開始用，所以傳 `ZETAS[1:]`），值是 Montgomery 形式，由 `R` 換回一般形式 |
| `lib.ntt.gs_schedule(...)` | Gentleman–Sande（inverse NTT） |

**範例 1：NTT（多項式、2 個模數）**

```python
from c2mix.spec import *
from c2mix.lib import ntt
from .params import Q, ZETAS              # 方案常數只出現在 targets/ 底下

t = Target("ntt", args={"r": InOut(Array("int16_t", 256))})
r, x = t.arg("r"), Indet("x")
inp = t.ghost("inp", poly([r[i].entry for i in range(256)], x))
t.pre(range=[abs_lt(r[i].entry, Q) for i in range(256)])
for k, blocks in enumerate(ntt.ct_schedule(256, Q, ZETAS[1:], R=2**16, layers=7), 1):
    c = t.cut("layer", k)
    c.range(abs_lt(r[i].at(c), (k + 1) * Q) for i in range(256))
    c.alg(eqmod(inp, poly([r[j].at(c) for j in range(b.lo, b.hi)], x),
                [Q, x**b.deg - b.zeta]) for b in blocks)
t.post(same_as=c)
```

**範例 2：多 limb Montgomery 乘法（整數、1 個模數）**

```python
from .params import P                     # 2**256 - 2**224 + 2**192 + 2**96 - 1
t = Target("fiat_p256_mul", args={"out1": Out(Array("uint64_t", 4)),
                                  "arg1": In(Array("uint64_t", 4)),
                                  "arg2": In(Array("uint64_t", 4))})
A, B, O = (limbs([t.arg(n)[i] for i in range(4)], 64) for n in ("arg1", "arg2", "out1"))
t.pre(range=[rng(0 <= A.entry < P), rng(0 <= B.entry < P)])
t.post(range=[rng(0 <= O.exit < P)],
       alg=[eqmod(O.exit * 2**256, A.entry * B.entry, [P])])
```

兩個範例用的是同一套核心，差別只在規格模組。

### 4.4 規格自檢（S1–S5）

| # | 檢查 | 失敗時 |
|---|---|---|
| S1 | 每個參照都能在指定時間點解析 | 報錯並停止 |
| S2 | 每個 `eqmod` 最多 2 個模數 | 報錯並停止 |
| S3 | `lib.ntt` 產生的規格：葉模數乘積 ≡ xⁿ+1 (mod q)、兩兩互質，每個父模數都等於兩個子模數的乘積 | 報錯並停止 |
| S4 | ghost 恰好綁定一次，而且只引用 entry 值 | 報錯並停止 |
| S5 | 規格在具體執行上成立 | 這就是 G4（§8） |

---

## 5. 前端與內部 IR

### 5.1 c2mix IR 的值

每個 SSA 值帶以下屬性：

- 名稱
- 寬度 w ∈ [1, 128]
- 有號性 s ∈ {signed, unsigned}：這是**解讀**，BV 本身沒有號
- 來源：已登記物件的元素、暫存值、witness 或 alias
- 原始碼位置（來自 `-g` 的 debug location）

LLVM IR 的整數是 signless，所以有號性依序這樣決定：

1. 已登記物件的元素：用登記時的 `is_signed`。
2. 暫存值：看產生它的運算。`sext`、`ashr`、`icmp s*` → signed；`zext`、`lshr`、`icmp u*` → unsigned。
3. 有 debug info 的具名區域變數：用 `DIBasicType` 的 encoding（`DW_ATE_signed` / `DW_ATE_unsigned`）。
4. 一個值在不同使用點需要不同解讀時，在該使用點插入 L10 橋接。

### 5.2 c2mix IR 指令集

`const`、`add`、`sub`、`neg`、`mul`、`shl k`、`ashr k`、`lshr k`、`sext`、`zext`、
`extract hi:lo`、`and`、`or`、`xor`、`not`、`cmp`（Bool）、`ite`、`marker(tag)`。

複製在執行時就消掉了（執行器的環境直接把 LLVM 值對應到 c2mix IR 值），軌跡裡沒有 `mov`。
只有有號性改變的地方會產生 L10。LLVM 沒有 `not` 指令，`xor x, -1` 在執行時轉成 `not`。

### 5.3 前端管線

```sh
CFLAGS="-O0 -Xclang -disable-O0-optnone -fwrapv -fno-strict-aliasing -g -I include"
# include 模式：只有 harness.c（它 #include 了上游 .c）
# link 模式：harness.c 與每個上游 .c 各編一次
for f in $SOURCES; do
  clang-18 $CFLAGS -S -emit-llvm "$f" -o "$(basename "${f%.c}").ll"
done
llvm-link-18 -S *.ll -o program.ll
opt-18 -passes=mem2reg -S program.ll -o program.m2r.ll
```

clang 一次給多個輸入檔又指定 `-o` 會直接報錯，所以要逐檔編譯再用 `llvm-link` 合併。
G2 的原生執行檔也從同一份 `program.m2r.ll` 編出來（`clang-18 program.m2r.ll runtime/c2mix_rt.c`），
確保比對的是同一份 IR。

- `-disable-O0-optnone`：否則 `mem2reg` 不作用（LF1）。
- `-fwrapv`：有號溢位的語意變成 wrap，與 BV 模型一致，並且不產生 `nsw`（LF2）。
- `mem2reg` 是唯一的 pass。它只把純量區域變數提升成 SSA，不改變運算。陣列仍在記憶體裡，交給執行器處理。

### 5.4 IR 解析器（支援子集）

解析器只接受下列指令。附錄 B 有完整的文法與運算元形式。

| 類別 | 指令 |
|---|---|
| 算術 | `add`、`sub`、`mul`、`shl`、`lshr`、`ashr`、`and`、`or`、`xor` |
| 轉型 | `trunc`、`sext`、`zext` |
| 比較與選擇 | `icmp`、`select` |
| 記憶體 | `alloca`、`load`、`store`、`getelementptr` |
| 控制流 | `br`、`switch`、`phi`、`ret`、`unreachable` |
| 呼叫 | `call`（定義在模組內的函式、runtime API、白名單 intrinsic） |

白名單 intrinsic：`llvm.dbg.*`（忽略）、`llvm.lifetime.*`（忽略）、長度為常數的
`llvm.memcpy.*` / `llvm.memset.*`（逐元素展開，型別必須一致）。

其他任何指令、型別或屬性一律拒絕，錯誤訊息要附上原始碼行號。

### 5.5 執行器語意

**狀態**

- 環境：LLVM 值 → 常數，或 c2mix IR 值。所有輸入都是常數的運算直接摺疊成常數。
- 記憶體：物件的集合（`alloca`、已登記物件、全域）。每個物件依元素型別切成格子，每格存一個值。
  指標值是具體的 `(物件, 位元組偏移)`。
- 呼叫堆疊：呼叫模組內的函式時 push frame，等於 inline。

**規則**

| 構造 | 處理 |
|---|---|
| `getelementptr` | 索引全是常數 → 算出具體偏移；否則 `E-DYN-INDEX` |
| `load` / `store` | 偏移必須對齊元素大小，存取型別必須等於元素型別（否則 `E-MIXED-ACCESS`）。`store` 讓該格產生新的 SSA 版本 |
| 對 `constant` 全域的 `load` | 直接摺疊成常數（LF3） |
| 二元運算、轉型 | 產生對應的 c2mix IR 運算。帶任何會產生 poison 的旗標（`nsw`、`nuw`、`exact`、`nneg`、`disjoint` 等；只有 GEP 的 `inbounds` 忽略）→ `E-POISON-FLAG`。位移量不是常數 → `E-VAR-SHIFT`。`sdiv`/`udiv`/`srem`/`urem` → `E-DIV` |
| `icmp` | 產生 `cmp` |
| `select` | 產生 `ite` |
| `br` / `switch`，條件是常數 | 直接走那一邊 |
| `switch`，條件依賴輸入 | `E-SYMBOLIC-BRANCH` |
| `br`，條件依賴輸入 | 計算直接後支配點，兩邊分別執行到那裡，再把兩邊不同的值與記憶體格用 `ite(cond, a, b)` 合流。兩邊都不能呼叫 `c2mix_cut`，合流巢狀深度 ≤ `max_merge_depth`（預設 8），否則 `E-SYMBOLIC-BRANCH`。迴圈頭的條件依賴輸入 → `E-SYMBOLIC-LOOP` |
| `phi` | 依實際走過的前驅區塊選值；在合流點由合流規則處理 |
| `call` runtime API | `c2mix_register` 建立命名物件；`c2mix_input` 讓物件的每格變成新的符號輸入；`c2mix_cut` 產生 `marker`；`c2mix_done` 標記 exit |
| `call` 其他外部函式 | `E-EXTERNAL-CALL` |
| 向量型別 | `E-VECTOR` |
| `extractvalue`、`insertvalue`、aggregate 型別的值 | `E-UNSUPPORTED` |
| 讀取從未寫入、也不是輸入的格子；運算元是 `undef` 或 `poison`（`mem2reg` 會把未初始化的純量變成 `undef`） | `E-UNINIT` |
| 步數超過 `max_steps` | `E-UNBOUNDED` |

**時間點**：`.entry` 是執行到呼叫入口函式那一刻的狀態；`.at((tag, k))` 是第 k 次執行
`c2mix_cut(tag)` 那一刻；`.exit` 是執行到 `c2mix_done` 那一刻。

---

## 6. Lowering

### 6.1 記號與整數編碼

⟦v⟧ 表示 v 依其有號性讀成的整數。

- **unsigned**：`(bv2nat v)`，Z3 對 bv2nat 的語意就是無號，正確。
- **signed**：alias `s__v`，定義在 range 段。v 在本段有 BV 定義時，緊接在該定義之後；v 是本段的輸入（entry 值，或前面的段留下的值）時，放在 range 段開頭、Rᵢ 之後：

```smt
(declare-const s__v Int)
(assert (= s__v (- (bv2nat v) (* 65536 (bv2nat ((_ extract 15 15) v))))))   ; w = 16
```

### 6.2 exactness 判定（D6）

區間分析在 IR 上前向傳播。每一段的起點是該段的範圍前提：第 0 段用 `pre.range`，
之後各段用前一個 cut 的 range 斷言。

會溢位的運算（add、sub、neg、shl、同寬 mul、窄化 extract）逐一判定：

- 區間落在目標型別可表示的範圍內 → **EXACT**：寫精確代數等式，並把 safety 義務寫進 range VC。
- 否則 → **SPLIT**：先用加寬運算得到精確值，再用 L9-SPLIT 拆成高位與低位。

判成 SPLIT 的運算，結果的區間取目標型別的完整範圍（因為結果會 wrap）。

`--exactness=split` 會強制全部走 SPLIT（除錯用）。每個運算的判定結果都寫進 manifest。

### 6.3 規則表

w 是寬度。「—」表示沒有這一項。

| 規則 | IR | range 段（BV） | algebraic 段 | safety 義務 | 新符號 |
|---|---|---|---|---|---|
| L1 | const | 內嵌 `#x…` | 內嵌 `(PConst n)` | — | — |
| L3 | `r = a ± b`、`r = −a`（EXACT） | `(= r (bvadd a b))` 等 | `⟦r⟧ = ⟦a⟧ ± ⟦b⟧` | 精確值落在 w-bit 範圍內 | — |
| L3′ | 同上（SPLIT） | 加寬到 w+1（L5）再 L9-SPLIT | 由 L5、L9 產生 | — | 高位 h |
| L4 | `r = a·b` 同寬（EXACT） | `(= r (bvmul a b))` | `⟦r⟧ = ⟦a⟧·⟦b⟧` | 乘積落在 w-bit 範圍內 | — |
| L4′ | 同上（SPLIT） | 加寬到 2w 再 L9-SPLIT | `⟦L⟧ᵤ + ⟦H⟧·2ʷ = ⟦a⟧·⟦b⟧` | — | H、L（即 golden 的 `mulH`/`mulL`） |
| L5 | 加寬運算（運算元的有效位數保證不溢位） | 原式 | 精確等式 | —（靜態成立） | — |
| L6 | `shl k` | 視同乘以 2ᵏ | 依 L4 / L4′ | 依 L4 | — |
| L7 | `ashr k` / `lshr k` | `(= r (bvashr x k))`、`(= l ((_ extract k-1 0) x))` | `⟦x⟧ = ⟦r⟧·2ᵏ + ⟦l⟧ᵤ` | — | 低位 l（H1 候選） |
| L8 | `sext` / `zext` | 原式 | `⟦r⟧ₛ = ⟦a⟧ₛ`（sext）；`⟦r⟧ᵤ = ⟦a⟧ᵤ`（zext） | — | — |
| L9 | 窄化到 w′（`trunc`、`extract` 低位）（EXACT） | `(= r ((_ extract w′-1 0) x))` | `⟦r⟧ = ⟦x⟧` | 值落在 w′-bit 的目標解讀範圍內 | — |
| L9′ | 同上（SPLIT） | 另加 `(= h ((_ extract W-1 w′) x))` | `⟦x⟧ = ⟦h⟧·2^w′ + ⟦r⟧ᵤ` | — | h（由 BV 定義，不是自由變數） |
| L9m | 遮罩 `r = x & (2^w′ − 1)`（寬度不變，仍是 W） | `(= r (bvand x mask))`，另加 `(= h ((_ extract W-1 w′) x))` | `⟦x⟧ = ⟦h⟧·2^w′ + ⟦r⟧ᵤ`（h 取 x 的有號性） | — | h（H1 候選） |
| L10 | 換有號性 | `(= b ((_ extract w-1 w-1) v))` | `⟦v⟧ᵤ = ⟦v⟧ₛ + 2ʷ·⟦b⟧` | — | 1-bit b（即 golden 的 `tmp…`，但這裡由 BV 定義） |
| L11 | `extract hi:lo`（lo > 0） | 拆成 L7 + L9 | 同左 | — | — |
| L12 | `ite(g, a, b)`（來自 `select` 或合流）；或遮罩 `(m & a) \| (~m & b)` | 原式；另加 `(= c (ite g #b1 #b0))` 或 `(= c ((_ extract 0 0) m))` | `⟦r⟧ = ⟦b⟧ + ⟦c⟧·(⟦a⟧ − ⟦b⟧)`，以及 `c·c = c` | 遮罩形式要求 m ∈ {0, ~0}（H2） | 1-bit c |
| L13n | `not`（來自 `xor x, -1`） | `(= r (bvnot x))` | `⟦r⟧ᵤ = 2ʷ − 1 − ⟦x⟧ᵤ`；有號時 `⟦r⟧ₛ = −1 − ⟦x⟧ₛ` | — | — |
| L13 | 其他位元運算、比較 | 原式 | **無**（結果在代數上是自由的） | — | 記 `W-ALG-FREE` |
| L14 | `marker(tag)` | 無敘述 | 無敘述 | — | 段落邊界 |

L2 保留不用（原本是 mov，已由執行器的 copy propagation 取代）。

**複製沿用 atom**（第 4 階段加入）：L8，以及 EXACT 或恆等的 L9，在代數層只說「⟦r⟧ = ⟦x⟧」。
這種式子不再輸出：r 在該讀法下直接沿用 x 的 atom（`Encoder.alias`），代數層裡根本不出現 r。
同一個值先被遮罩（L9m）、再在同一個位元位置位移（L7）時，位移結果沿用遮罩的高位 witness，
不再另立一條拆分式與低位 witness；低位的 hint 候選改看遮罩的結果。沿用只是把等式代入消去，
所以 sound 與否取決於那條恆等式本身：它們記在 `seg.alias_eqs`，A1.1 的引理把它們當目標證明、
A1.2 照樣突變，A1.3 的 fuzz 與 G3 在真實執行上逐條求值。r 若在另一種讀法下被用到，L10 橋接
照常產生，一端就是沿用的 atom。實測：Kyber `ntt` 一層的代數敘述 2817 → 1537 條，
bin/main 164 秒 → 92 秒。副作用也要記下：`fiat_p256_cmovznz` 的 **omit** 模式（沒有 hint，要
bin/main 自己從 range 段找出遮罩位元就是 arg1）從 0.25 秒變成 20 秒——兩個檔在邏輯上等價，差別在
bin/main 的搜尋；emit 模式（關卡）不受影響。這是 `Options.copy_alias` 可以關掉的原因。

每個 1-bit 符號都加上 `c·c = c`（CryptoLine 對 carry 的作法）。這條等式永遠為真，
所以 sound，而且能幫 Gröbner 基底計算。

### 6.4 hint：把 range 事實轉進代數層

某些代數證明需要只有 range 層才知道的事實，最典型的是 Montgomery 約簡的 `lo = 0`（F7）。
核心會自動找出這類事實：

**候選**

- H1：L7 / L9′ / L9m 的低位 l 或高位 h 等於常數。
- H2：L12 的遮罩 m ∈ {0, ~0}。
- H3：任何 1-bit 符號等於常數。
- H4：**兩個 1-bit 符號恆等**（2026-09-23 加入）。條件減法會用到：`select` 的條件位元就是它所選的那個減法的借位，兩者在 range 模型裡是同一個位元，但代數層看不到這件事，缺了它 T2b 的 VC 就不成立（實測 `sat`）。加上之後 0.24 s `unsat`。判定與其他候選一樣：在 range 模型上用 z3 證，證不出來就不輸出；輸出時依兩個符號各自的讀法寫等式（1-bit 的有號讀法是無號讀法的相反數）。
- H5：**兩個 SPLIT 窄化丟掉的量相等**，⟦x⟧ − ⟦r⟧ = ⟦x′⟧ − ⟦r′⟧（第 3 階段加入）。在寬型別算完再存回窄型別會 wrap；程式接著把運算反過來做時，第二次 wrap 剛好抵銷第一次，同餘式只因為這件事才成立。Barrett 約簡就是標準例子：`t *= q` wrap 一次，`a - t` wrap 回來。CryptoLine 在 `03_barrett.cl` 裡是人工寫下這條（`assert true && (sext r 16) = a32 - tq;`），c2mix 把它變成和其他候選一樣由 z3 判定。缺了它 `cbmc03_barrett` 與 `kyber_barrett` 都是 `sat`，加上之後分別 0.35 s、0.4 s `unsat`。
- H6：**一個值等於它自己被拆出來的那些 1-bit 符號的加權和**，⟦v⟧ = Σ 2ⁱ⟦bᵢ⟧（第 3 階段加入）。位元運算與比較在代數層是自由的（L13），所以「把乘數一位一位拆開再累加」這種程式，代數層完全沒有 v 與 bᵢ 之間的連結。判定分兩步，都在 range 模型上用 z3：先逐位找出等於 `extract(v, i, i)` 的 1-bit 符號，再確認 v 高位為 0。`cbmc04_loop_mul` 缺了它跑不完（> 10 分鐘），加上之後 0.13 s `unsat`。

**實作上的注意**（第 3 階段實測）：只有**證出來的**候選才可以去跟 encoder 要 atom。
在還沒證明前就要 atom，會替那些最後被丟掉的候選留下 alias 與 L10 橋接，等於憑空多出
未知數：`cbmc04_loop_mul` 因此多了 8 個橋接與 8 個 1-bit 符號，`bin/main` 從 0.13 秒
變成 10 分鐘以上跑不完。

**判定**

在該段的 range 模型上用 z3 證明 v = k（逐一證，每個候選有 timeout）。證得的候選就是 hint。

**判定的實作**（第 4 階段加入，`vc/prover.py`）：Kyber `ntt` 一層有 128 個 butterfly，把整段
range 模型連同每個候選送給 z3，光是 hint 就跑十分鐘以上；fiat `p256_mul` 更是在第一批候選就卡住。
改成下面四件事之後，Kyber `ntt` 整個 build 6 秒：

1. **樣本過濾**：先取 16 筆滿足前置條件的真實執行（一半取在各輸入區間的端點，進位與借位才會
   發生），算出段內每個符號的值。某筆執行上就不成立的候選，不可能證得出來，不送 z3。
   樣本只用來**丟掉**候選，z3 仍是唯一的判定者。
2. **切片**：每個候選只帶它的 cone of influence：它提到的符號的定義（遞移地），以及碰到這些
   符號的前提。少帶前提只會證不出來，不會證出假的；而 cone 以外的符號各自只被定義一次、
   沒有其他限制，所以切片也不會漏掉任何需要的前提。
3. **加深**：多數候選是局部的——Montgomery 那一步的低 limb 為 0，與乘數怎麼算出來無關——
   但多 limb 乘法後段的值，完整 cone 裡有前面所有 64×64 乘積，z3 要全部 bit-blast。所以先在
   截斷到 4、8、16 層的 cone 上試（更遠的符號留成自由變數，timeout 2 秒），失敗的才加深，最後
   才用完整 cone（超過 400 條敘述就放棄，只損失一個 hint）。截斷的切片仍是模型的子集，證得就是
   證得。實測 `lo64(x + lo64(x·(2⁶⁴−1))) = 0` 在 x 自由時 0.02 秒，帶上 x 的定義鏈則幾分鐘跑不完。
4. **批次**：切片後的查詢以 `(reset)` 隔開、各自帶 timeout，分給數個 z3 行程平行跑。

每個 hint 記下證得它的深度，range VC 拆分時（§7.4）用同一個切片重證。

**兩種輸出模式**

| 模式 | `cutN.smt2` | `cutN.range.smt2` | manifest |
|---|---|---|---|
| `--hints=emit`（CryptoLine `assume` 的作法） | range 段放 `(assert true)` 佔位；algebraic 段放 `(assert (eqP ⟦v⟧ (PConst k)))` | 放入 hint 的義務 | 記錄 |
| `--hints=omit`（與 golden `pqclean_kyber768_avx2_noAssume` 相同的作法） | 不放 | 不放 | **仍然記錄**，方便比較 extend_z3 自己發現了哪些 |

**soundness**：hint 只在 z3 證出來之後才會輸出，而且 range VC 會再獨立驗證一次（G5）。
拿掉 hint 只會讓 VC 更難證，不會讓它 unsound。

---

## 7. VC 組裝與輸出格式

### 7.1 切段

程式軌跡記為 s₁…sₙ，marker 位置為 m₁ < … < m_K。

- 段 S₀ = s₁…s_{m₁}，Sᵢ = s_{mᵢ+1}…s_{mᵢ₊₁}，最後一段 S_K 到 `c2mix_done`。
- 斷言集合 C₀ = pre，C₁…C_K = 各 cut，C_{K+1} = post。每個 Cᵢ 分成 range 部分 Rᵢ 與代數部分 Aᵢ。

| 檔案 | 前提 | 程式 | 目標 |
|---|---|---|---|
| `cut{i}.smt2` | Rᵢ、Aᵢ、攜帶的事實 | BV(Sᵢ) 與 ALG(Sᵢ) | ¬Aᵢ₊₁ |
| `cut{i}.range.smt2` | Rᵢ、攜帶的 range 事實 | BV(Sᵢ) | ¬(Rᵢ₊₁ ∧ safety(Sᵢ) ∧ hints(Sᵢ)) |

### 7.2 事實攜帶

SSA 值不會被改寫，所以先前證過的斷言永遠成立。VCᵢ 的前提是 Cᵢ 加上「和 Sᵢ 或 Cᵢ₊₁ 有關」的
早期結論；「有關」指斷言提到 Sᵢ 讀到的或 Cᵢ₊₁ 提到的某個 SSA 值，ghost 不算。

range 事實也用同一條規則攜帶，放在 Rᵢ 的位置；區間分析（§6.2）的起點同樣包含它們。

選項：`--carry=relevant|previous|all`，預設 `relevant`。

soundness 只要求一件事：每個被攜帶的事實都是某個 j < i 的 VCⱼ 的結論（G9）。
這個規則不嘗試複製 CryptoLine 內部的攜帶規則，所以和 golden 的比較放在數學層（§8.3）。

### 7.3 mix 檔格式（`cutN.smt2`）

```
(set-info :smt-lib-version 2.0)
(set-logic ALL)
; variable declaration
(declare-const …)                        每個符號恰好一次，依名稱排序
; range precondition and program ␣       ← 行尾有一個空白，與 golden 相同
(assert <Rᵢ 與攜帶 range 事實的合取，空則 true>)
<本段輸入值的 alias 定義>
<BV 敘述，依程式順序；alias 定義緊接在對應的 BV 定義之後>
; algebraic precondition and program
(assert <Aᵢ 與攜帶事實的合取，空則 true>)
<ghost 綁定，只出現在 entry 段>
<代數敘述，依程式順序；emit 模式的 hint 放在產生點>
; postcondition
(assert (not (and <Aᵢ₊₁>)))
; check
(check-sat)
(exit)
```

| # | 規則 |
|---|---|
| M1 | 必須有 `(set-logic ALL)`，prelude 從這行後面插入（F2） |
| M2 | 不得宣告 `Poly` datatype，也不得宣告 `eqP`/`eqmodP*` |
| M3 | 只用 `(Poly Int)`；判斷式只用 `eqP`、`eqmodP1`、`eqmodP2` |
| M4 | 不定元只用 `(PVar "…")`；BV 值只能透過 `(bv2nat v)` 或 Int alias 進入 `PConst` |
| M5 | `PConst` 的引數必須是原子：數字、`(- n)`、`(bv2nat v)` 或 alias |
| M6 | 目標恰好一條 assert。沒有代數目標時寫 `(assert (not (and true true)))`（同 golden），並在 manifest 標 `trivial: true` |
| M7 | 符號只用 `[A-Za-z_][A-Za-z0-9_]*`，不用 `\|…\|`。命名規則：已登記物件的元素 `<name>_<idx>_<ver>`（name 是登記名；idx 十進位、補零到該物件的最大位數，例如 `r_017_3`）；純量物件 `<name>_<ver>`；暫存值 `t<n>`；witness `w<kind><n>`；alias `s__<name>`。名稱衝突時報錯，不偷偷改名 |
| M8 | BV 常數寫 `#x…`（寬度為 4 的倍數時）或 `#b…`；Int 常數寫十進位，負數寫 `(- n)` |
| M9 | 決定性：相同輸入產生位元組相同的輸出。不用 hash 順序，不用亂數名稱 |
| M10 | 五行 section 註解的字面與 golden 完全相同，包含 range 那行的尾端空白 |

**lint 的兩個 profile**

| profile | 檢查什麼 | 用在哪裡 |
|---|---|---|
| `strict` | M1–M10 全部 | c2mix 自己的輸出（G1） |
| `consumer` | 只把「extend_z3 讀不進來或會讀錯」的情況當 error：M1、M2、M3、M6、M10，以及所有符號都有宣告。其他規則降為 warning | golden 與其他外部語料（A0.1） |

golden 用了 `(PConst (bv2int v))`（違反 M5），宣告也沒有排序（違反 §7.3 的排序要求），
所以在 `strict` 下一定是 error，只能用 `consumer` 檢查。

### 7.4 range VC 檔（`cutN.range.smt2`）

```
(set-logic QF_BV)
<宣告>
(assert Rᵢ)
<BV(Sᵢ)>
(assert (not (and Rᵢ₊₁ safety(Sᵢ) hints(Sᵢ))))
(check-sat)
```

safety 義務一律寫成 QF_BV：運算元依有號性加寬（加減法加寬到 w+1，乘法加寬到 2w），在加寬後的寬度上比較上下界。

檔案太大時，`--range-split=N` 會把義務拆成 N 個檔案（target 可以在 `target.toml` 的
`[build] range_split` 給預設值）。拆分後的格式（第 4 階段）：

- 共用敘述的義務（cone 有交集）分在同一個檔，各檔依工作量平衡。
- **每條義務自成一個查詢**，只帶它的 cone（§6.4 的切片），查詢之間以 `(reset)` 隔開。
  G5 要求檔內每個查詢都回答 `unsat`，而且回答數等於 `(check-sat)` 數。
- cone 很大（> 60 條敘述）的義務，assembler 先在截斷的 cone 上試證（同 §6.4），記下最淺的
  成功深度並用那個切片輸出；都證不出來就用完整 cone，由 G5 判定。hint 用它自己被證得的深度。

這樣做成立：每個查詢從段模型的一個子集證明它的義務，所以在整個模型上也成立；所有查詢合起來
涵蓋全部義務，和一個檔案是同一個證明。逐條問不只是整齊：Kyber 一個 butterfly 的 12 條義務，
合成一個否定合取要 16 秒，逐條各在 0.2 秒內；整層 128 個 butterfly 合成一個檔則超過 10 分鐘。

### 7.5 `manifest.json`

- 工具與版本：c2mix commit、clang/opt 版本、完整命令列、spec 與原始檔的 hash。
- 每個 cut：
  - 檔名。
  - 各段的宣告數與 assert 數。
  - 模數清單與界線。
  - hint：已證明的、已輸出的。
  - 每個運算的 EXACT / SPLIT 判定。
  - `W-ALG-FREE` 的數量。
  - 合流次數與最大深度。
  - `trivial` 旗標。
- 符號對照表：SMT 名稱 ↔（登記物件、索引、SSA 版本、LLVM 值名、原始碼行號）。

---

## 8. 驗證關卡（每個階段共用）

### 8.0 Poly 理論的語意約定

prelude 裡的 `eqP`、`eqmodP1`、`eqmodP2` 在 SMT-LIB 裡是未解釋函式，本身沒有語意。
c2mix 採用以下語意，G3、G4 與 §8.2 都以它為準：

- Poly 值是 ℤ[X] 的元素，X 是所有 `PVar` 名稱的集合。`PConst n` 是常數多項式；
  `PAdd`、`PSub`、`PMul`、`PNeg`、`PPow` 是對應的多項式運算。
- 型別為 `(Poly Int)` 的未解釋常數（ghost）是 ℤ[X] 中的某個元素，由模型給值。
- `eqP(p, q)` ⟺ p = q（多項式恆等）。
- `eqmodP1(a, b, m)` ⟺ a − b ∈ ⟨m⟩；`eqmodP2(a, b, m₁, m₂)` ⟺ a − b ∈ ⟨m₁, m₂⟩（ℤ[X] 中的理想）。

在這個語意下，「VC 是 `unsat`」才等於「前提蘊含目標」，§8.2 的論證依賴這一點。
這也是 D8 不採用 `(PPow g 2)` 形式的原因。

### 8.1 關卡一覽

| 關卡 | 檢查什麼 | 怎麼檢查 | 抓得到的錯 |
|---|---|---|---|
| **G1** 格式契約 | M1–M10 | `c2mix lint` | 輸出格式錯誤 |
| **G2** 前端保真 | 軌跡的語意等於 C 的語意 | 差分執行：用同一個 clang-18、同樣的 `-fwrapv`，把 harness 與 `runtime/c2mix_rt.c` 編成原生執行檔，和 c2mix IR interpreter 比對**每個 cut 的快照**與最終輸出。輸入：總輸入位元 ≤ 24 時窮舉，否則 10⁵ 筆亂數加邊界語料，**不受前置條件限制**。另外把原生版本以 `-O0` 和 `-O2` 各編一次，結果不同時報 `W-UB-SENSITIVE`（程式依賴 UB 或實作定義行為） | 解析器與執行器的錯 |
| **G3** 軌跡一致 | 真實執行是每個 VC 前提的模型 | 對滿足前置條件的執行，算出每個 VC 所有符號的值（BV 值、alias、witness、h/l、ghost 多項式），逐條求值所有非目標斷言，全部必須為真。BV 與 Int 部分用 SMT-LIB 標準語意，Poly 部分用 §8.0 的語意；前提裡的 `eqmod` 判定方式與限制同 G4。自寫 evaluator；另抽 1% 用 z3 交叉驗證 BV 與 Int 部分（z3 無法判定 `eqP` 系列） | vacuity（前提矛盾）、有號性錯、規則錯 |
| **G4** 規格成立 | 規格在真實執行上為真 | 在執行上逐一求值 pre ⇒（每個 cut 斷言、post）。整數 `eqmod` 用整除判定；(質數 q, 首一多項式 m) 的 `eqmod` 在 F_q[x] 上約簡後判定；模數是程式變數時代入具體值。其他形式回報 `unsupported-eval`，必須在 `target.toml` 註明豁免理由 | 規格寫錯 |
| **G5** range 義務 | safety、界線、hint 都成立 | 每個 `cutN.range.smt2`（拆分時是每個 `cutN.range.K.smt2`）用 `z3` 求解，檔內每個查詢都必須 `unsat`（§7.4） | 溢位、界線錯誤 |
| **G6** 代數目標 | 每段的目標成立 | 每個 `cutN.smt2` 用 `bin/main` 求解，必須 `unsat`（flag 見 §10）。`sat` 只代表「沒證出來」，不是反例（F10），不能據此判定程式或規格有錯 | 程式或規格錯（也可能是求解器限制，見 R6） |
| **G7** 突變 | 測試真的有鑑別力 | C 突變：常數 ±1、`+` 和 `−` 互換、運算元互換、刪除敘述、索引差一、常數表換錯項。規格突變：換錯 ζ、界線改緊。每個突變都必須被某個關卡擋下，擊殺率 100%；等價突變要在 `target.toml` 寫明理由 | 測試太弱 |
| **G8** 決定性 | 可重現 | 跑兩次，輸出位元組完全相同 | 隱藏的非決定性 |
| **G9** cut 鏈完整 | 沒有未經證明的前提 | 用腳本掃 manifest：每個被攜帶的事實都是某個較早 VC 的結論或 pre，而且每個 VC 都通過 G5 與 G6 | 攜帶邏輯錯 |
| **G10** 核心通用 | 核心沒有方案知識 | `grep -riE 'kyber\|dilithium\|saber\|mceliece\|p256\|25519\|3329\|8380417' c2mix/` 必須 0 筆 | 通用性退化 |

### 8.2 soundness 論證

**主張**：如果每個 cut 都通過 G5 與 G6，那麼對每個滿足前置條件的輸入，程式（依 clang 產生的
LLVM IR 語意）滿足後置條件。

**證明梗概**：對段落做歸納。第 i 段的前提 Rᵢ ∧ Aᵢ 由 VCᵢ₋₁（或 pre）保證；攜帶的事實由
G9 保證。在這個前提下：

- BV(Sᵢ) 就是程式語意（執行器的軌跡）。
- ALG(Sᵢ) 的每一條都被 BV(Sᵢ) ∧ safety 蘊含（規則引理 A1.1）。
- safety 與 hint 由 G5 證明。
- 所以 Aᵢ₊₁ 成立（G6），Rᵢ₊₁ 也成立（G5）。

**信任基礎與假設**：clang 從 C 到 LLVM IR 的翻譯、extend_z3、Z3；extend_z3 的推理與 §8.0 的語意一致；規則引理只在有限寬度上證明（A1.1），128-bit 乘法只做了性質測試。解析器與執行器不在信任基礎裡，
由 G2 在有限樣本上對照原生執行（兩者用同一個 clang，所以對照的是「IR 的執行」這一段）。

G3、G4、G7 不在這個證明裡，它們擋的是另一類問題：

- 前提矛盾造成 vacuous 的 `unsat`（G3）。
- 規格本身寫錯（G4）。
- 測試沒有鑑別力（G7）。

### 8.3 golden 比對的層級

| 層級 | 比什麼 | 用在哪裡 |
|---|---|---|
| 格式層 | 兩組 golden 的 24 個檔案讀入再寫出 | 第 0 階段 |
| 數學層 | 不同實作、同一個數學命題：Kyber ref C vs Kyber AVX2 組語；fiat-crypto P-256 C vs OpenSSL P-256 組語。比模數樹、界線序列、目標形狀，**不比文字** | 第 4、5 階段 |

---

## 9. 分階段計畫

**回歸規則**：任何階段出口之後，只要核心有改動，就要重跑所有已完成階段的驗收（`make accept-all`）。

### 9.0 目標矩陣

| 目標 | 階段 | 寬度 | 解讀 / 模數 | 主要考驗 | golden |
|---|---|---|---|---|---|
| `cbmc_small` 01–04（只用 C 原始碼） | 3 | 8/16/32 | 整數 | cast、算術右移、小迴圈 | — |
| Kyber `montgomery_reduce`、`barrett_reduce`、`fqmul` | 3 | 16/32 | 整數 `eqmod` | SPLIT、H1 | — |
| Dilithium `montgomery_reduce`、`reduce32` | 3 | 32/64 | 整數 `eqmod` | 64-bit 乘積、R = 2³² | — |
| fiat p256 `addcarryx_u64`、`subborrowx_u64`、`mulx_u64`、`cmovznz_u64` | 3 | 64/128 | 整數 | carry、`i128`、L12 遮罩 | — |
| Kyber ref `ntt` | 4 | 16/32 | 多項式，2 個模數 | 256 元素陣列、7 個 cut | `pqclean_kyber768_avx2_noAssume`（數學層） |
| Dilithium ref `ntt` | 4 | 32/64 | 多項式，完全分解 | 8 個 cut、一次因式 | — |
| fiat `p256_mul`、`p256_sub`、`p256_opp`、`p256_to_montgomery`、`p256_from_montgomery` | 4 | 64/128 | 4-limb 整數 | Montgomery、carry chain、條件減法 | `openssl/ecp_nistz256` 的 `mul_mont`、`sub`、`neg`、`to_mont`、`from_mont`（數學層） |
| fiat `curve25519_carry_mul` | 4 | 64/128 | 5-limb 非飽和 | radix 2⁵¹、mod 2²⁵⁵−19 | — |
| held-out × 5 | 5 | — | — | 通用性 | — |

---

### 第 0 階段：格式層（完全不碰 C）

**產出**：`c2mix/mixfmt/{reader,writer,lint}.py`、`c2mix lint`、`c2mix roundtrip`、lint 規則文件。

**驗收**

- **A0.1 lint golden**：對兩組 golden 共 24 個檔案跑
  `c2mix lint --profile=consumer --baseline tests/phase0/lint-baseline.json`。

  通過標準：0 個 error，warning 與 baseline 完全一致。已知一定會出現的 warning（2026-09-22 實測）：
  - Kyber：`W-BV2INT`（全部 15 檔）、`W-INDET-BV`（cut1–14 的 `x_0` 宣告成 `(_ BitVec 1)`）、
    `W-TRIVIAL-GOAL`（cut7、cut14）、`W-DECL-ORDER`（全部 15 檔）。
  - OpenSSL：不會有 `W-BV2INT`、`W-INDET-BV`、`W-TRIVIAL-GOAL`（只用 `bv2nat`、沒有不定元、沒有平凡目標）。

  其餘降級規則的 warning 以第一次執行的結果為準。baseline 人工審過之後 commit。其他語料也可以拿來跑 lint 當參考，但結果不列入關卡。
- **A0.2 round-trip**：24 個 golden 檔案都要滿足 `write(read(f))` 在正規化後和 f 相等，
  而且 `bin/main` 對寫回的檔案給出和原檔相同的結果（全部 `unsat`）。flag 依 `regression_76` 的分組：
  Kyber 加 partition prepass，OpenSSL 不加。
- **A0.3 負面語料**：每條 lint 規則各準備一個違規檔，每個檔只觸發它自己那一條。
- **A0.4 編碼 A/B**（本階段最重要的風險排除）：
  - 用 `signed_alias.py` 把 Kyber noAssume 轉成 alias 編碼，用相同 flag 跑 `bin/main`，
    記錄結果、時間、MaxRSS，並和 F6 比較。OpenSSL 沒有有號值，不需要這項 A/B。
  - 在 Kyber cut0（有 ghost 綁定）與 cut1（ghost 只出現在前提與目標）上，比較 ghost 的直接綁定、內嵌與 `legacy-pow2` 三種形式。直接綁定可解 → 維持 D8；否則改用內嵌。

  **決策關卡**：alias 版必須全部 `unsat` 才維持 D4；做不到的話，先調查清楚才能進第 1 階段。

**出口**：A0.1–A0.3 通過；A0.4 的結論寫進 D4 與 D8。

---

### 第 1 階段：IR 與雙模型 lowering（手寫 IR，不碰 C）

**產出**：c2mix IR（`ops`、`interp`、`intervals`）、規則 L1–L14、alias / witness 產生器、引理產生器。

**驗收**

- **A1.1 規則引理**：對每條（規則 × 寬度 × 有號性 × EXACT/SPLIT）產生下面這種檔案，
  用 `z3` 求解必須 `unsat`：

  ```
  BV 定義 ∧ alias 定義 ∧ safety ⇒ 代數等式        （代數側的 eqP 換成 Int 上的 =）
  ```

  引理由 lowering 程式碼直接產生，驗的是實際會輸出 VC 的那條路徑。

  **實測後修正（2026-09-23，見 F9）**：上面這種混合式（bv2nat、Int alias、Int 非線性）
  z3 只有在 w = 4 算得完，w ≥ 8 就逾時，附錄 A 的 16-bit 範例也一樣。因此 A1.1 分成兩層：

  | 形式 | 內容 | 寬度 |
  |---|---|---|
  | `mixed` | c2mix 實際輸出的編碼，如上式 | w = 4（涵蓋所有規則） |
  | `bv` | 同一條引理在 QF_BV 的像：⟦v⟧ 換成加寬到 N = 2·maxw + 8 的 BV，Int 運算換成 BV 運算。N 比任何中間值都寬，所以兩者等價 | w = 4, 8, 16, 32, 64 |

  128-bit 的加減、位移、擴展與窄化用 `bv` 形式證。**乘法**在 w = 64 與 w = 128 兩種形式都
  逾時（QF_BV 也要 bit-blast 128/256-bit 乘法），改用 10⁶ 筆的性質測試（邊界值全配對加亂數，
  檢查的是實際輸出的敘述），並把這個缺口記為已知限制。細節見 `docs/lemmas.md`。
- **A1.2 引理突變**：每條規則至少 3 個突變（2 的冪次錯、一個運算元的有號性錯、漏掉 witness 或高位項、
  safety 界線差一），每個都必須讓引理變成 `sat`。突變只改規則自己產生的敘述。
  有些位置的正負號被引理自己的敘述釘死（例如無號 EXACT 左移，safety 蘊含最高位為 0），
  換讀法不會改變意義；這種等價突變由 z3 機械判定（問「這個值的最高位可以是 1 嗎」，
  `unsat` 即為釘死），在報告裡與 killed 分開計數。
- **A1.3 模糊測試**：1000 支隨機 IR 程式（長度 20–200、寬度混合、涵蓋所有運算）× 100 組輸入，
  以 G3 的方式求值所有輸出的斷言，全部必須為真。
- **A1.4 區間分析**：同一批執行中，每個具體值都必須落在分析得到的區間內。
- **A1.5 golden 樣式**：依 Kyber AVX2 `ntt.S` 手寫一條 butterfly lane 的 IR，用 `--int-encoding=bv2int`
  輸出，代數敘述在改名之後要和 golden cut0 的樣式相同：`mulL + mulH·65536 = …` 的拆分，
  以及 `tmp` 符號橋接。
- **G10**：從本階段開始每次 commit 都檢查。

**出口**：以上全部通過。

---

### 第 2 階段：規格 DSL 與 VC 組裝（手寫 IR，不碰 C）

**目標**：用 Python 測試輔助程式建出 IR，涵蓋每一種解讀：

| 目標 | 內容 | 考驗 |
|---|---|---|
| T2a | 小型 NTT：n = 8、q = 17、3 層（完全分解），Montgomery R = 2¹⁶ | 多項式解讀、2 個模數、cut |
| T2b | 2-limb 模加法：radix 2³²、p = 2⁶¹ − 1，含 carry 與條件減法 | limbs、carry、L12 |
| T2c | 純量 Montgomery 約簡（和 `cbmc_small` 02 是同一支程式） | H1 hint |

**驗收**

- **A2.1**：S1–S4 通過。規格突變（ζ 錯、少一個區塊、3 個模數）必須被 S 檢查擋下。
- **A2.2**：G3、G4 在 1000 組滿足前置條件的輸入上通過。
- **A2.3**：`--hints=emit` 模式下 G5、G6 全部 `unsat`；`--hints=omit` 只記錄結果。
- **A2.4**：G7，每個目標 10 個 IR 突變，擊殺率 100%。
- **A2.5**：G8、G9。

**出口**：以上全部通過。

---

### 第 3 階段：LLVM 前端（解析器、執行器、純量函式）

**目標**：§9.0 表中階段 3 的四列。上游來源在 vendoring 時固定 commit，寫進 `target.toml`。

**驗收**

- **A3.0 工具鏈實測**（本階段第一件事）：安裝 clang-18 / llvm-18，逐條確認 LF1–LF4，
  結果寫回 §2.0 的狀態欄。任何一條不成立，先修改規格（§5.3–§5.5）再繼續。
  另外統計所有第 3、4 階段目標的 IR 用到哪些指令，確認都在 §5.4 的子集內。
- **A3.1**：G2，0 筆不一致。可以窮舉的（例如 `barrett_reduce` 的 2¹⁶ 個輸入）就窮舉。
- **A3.2 解析器 round-trip**：對所有目標的 `.ll` 先用 `opt-18 -strip-debug` 去掉 debug metadata，
  解析後重新印出，`llvm-as-18` 必須接受，而且 `llvm-diff-18` 和原檔比較沒有差異。
  行號另外抽樣檢查：隨機取 100 條指令，解析器記錄的行號必須等於 `!dbg` 指向的 `DILocation`。
- **A3.3**：G1、G3、G4、G8。
- **A3.4**：`--hints=emit` 模式下 G5、G6 全部 `unsat`；`--hints=omit` 只記錄結果。
- **A3.5 參考對照**（只報告，不設關卡）：把 `cbmc_small` 01–04 的輸出和同目錄的 `cv` `mix_0` 並列
  （各段敘述數、`bin/main` 結果）。這組未確認正確，兩者不一致時要逐一查明原因，
  但不能拿它判定 c2mix 是對是錯。
- **A3.6**：G7。參考 `cbmc_small/mutants` 的突變種類（改模數、拿掉 `lo = 0` hint），再加上
  運算子突變，擊殺率 100%。
- **A3.7 拒絕語料**：除法、動態索引、不同型別存取同一塊記憶體、浮點、輸入相依的迴圈、
  無法合流的分支、遞迴、未定義的外部函式、向量型別。每個都要回傳指定的錯誤碼、附上原始碼行號，
  而且不產生任何輸出檔。
- **A3.8 前端穩健性**：拿 20 支無關的 C 程式編成 IR 去跑前端。結果只能是成功，
  或以指定錯誤碼失敗並指出是哪個構造；不准 crash，也不准默默丟掉東西。
- **A3.9 合流**：含輸入相依 `?:` 與 `if/else` 的測試程式（例如 fiat `cmovznz` 的分支寫法變體），
  G2、G3 通過，manifest 的合流統計正確。

**出口**：以上全部通過。

**實作結論（2026-09-23）**

目標共 14 個：`cbmc_small` 01–04、Kyber `montgomery_reduce`/`barrett_reduce`/`fqmul`、
Dilithium `montgomery_reduce`/`reduce32`、fiat P-256 的四個原語，加上 A3.9 的
`merge_cmov`（同一個條件選擇分別用 `if`/`else` 與 `?:` 寫）。LF1–LF4 全部成立，結果寫回
§2.0；14 個目標的 IR 只用到 §5.4 子集內的指令。

這個階段逼出五件核心的事，每一件都是通用規則，不是方案特例（G10）：

1. **hint H5、H6**（§6.4）。Barrett 的兩次 wrap 互相抵銷、把乘數一位一位拆開再累加，
   這兩種形狀在代數層都缺一條連結。
2. **L12 的遮罩形式**（§6.3 早就列了，第 3 階段才實作，見 `lower/idioms.py`）。
   `(m & a) | (~m & b)` 之前整個落在 L13（代數自由），fiat 的 `cmovznz` 因此在代數層
   完全沒有結論。

   **只有形狀是不夠的**：m 真的是全 0 或全 1 時等式才成立，否則等於在代數模型裡寫下一條
   假敘述，VC 會 vacuous 地 `unsat`。第一版只把「m ∈ {0, ~0}」當 safety 義務就套用規則，
   A1.3 的隨機程式立刻抓到（隨機的 `or` 湊出這個形狀，m 卻不是遮罩）。改成區間分析多帶一個
   「遮罩」格：`neg` 一個界線在 [0,1] 的值、`sext` 一個 1-bit 值會產生遮罩，之後 `not`、
   與另一個遮罩做位元運算、`sext`、取低位欄位都保持這個性質（`zext` 不保持）。fiat 的
   `0 - (!(!c))` 整條鏈剛好走完這些。義務仍然寫進 range VC，和 EXACT 一樣由 G5 複驗；
   它是冗餘的，所以 A1.2 把「拿掉這條義務」判為等價突變（由 z3 認證）。
3. **L10 橋接的觸發條件**。之前只有在「同一個 Value 被要求另一種讀法」時才發出；同一個
   名字以兩個不同有號性的 Value 分別被讀時（執行器換讀法就會這樣），兩個 atom 之間沒有
   任何關係，代數層等於把一個值拆成兩個互不相干的未知數。`fiat_p256_subborrowx` 就是
   因此證不出來。改成由 `atom()` 記錄讀法、第二種讀法出現時補上橋接。
4. **橋接的符號位若已知就不要留 witness**。改好 3 之後，多出來的 1-bit witness 讓
   `cbmc04_loop_mul` 從 0.13 秒變成十分鐘跑不完。區間分析能定出符號位時就直接代常數，
   並把「符號位等於這個常數」寫進 range VC 當 safety 義務（和 EXACT 的作法一樣）。
   注意區間是對「定義時的讀法」說的，換讀法的 Value 不能直接拿來用。
5. **只替證出來的 hint 候選要 atom**（§6.4 的注意事項）。

另外 G5 抓到一個規格錯誤：`dilithium_reduce32` 的前置條件只照抄上游註解的上界
（`a <= 2^31 - 2^22 - 1`），下界放成 −2³¹ 就不成立——a = −2143289344 會得到
r = −6283009，比同一段註解保證的界線多 1。改成對稱的 |a| ≤ 2³¹ − 2²² − 1 之後通過。

追過呼叫點之後確認這個界線是**緊的**，而且不該換成呼叫點的界線（推導寫在
`targets/dilithium_reduce32/params.py`）：上游那句上界其實是「`a + (1<<22)` 不溢位」的
條件，不是幅度條件。窮舉 [−2³¹, 2³¹ − 2²² − 1] 全部輸入，失守的**只有** −(2³¹ − 2²²) 這一個
（−2³¹ 本身反而成立，r = −2096896）；上端 2³¹ − 2²² − 1 恰好得到 r = 6283008。所以對稱界線
是「包含 0、後置條件成立」的最大區間，兩端都一格放寬不得。實際的六個呼叫點（`ref/sign.c` 的
`polyveck_reduce`/`polyvecl_reduce`）中，三個的輸入是 `polyvec_matrix_pointwise_montgomery`
的輸出，幅度 < `L·Q` 或 `(L+1)·Q`（由 `montgomery_reduce` 的 |r| < Q 累加 L 次而來）：
vendor 的 mode 2（L = 4）最多 5Q ≈ 2^25.3，距離界線 51 倍；mode 5（L = 7）的 8Q = 2²⁶ 也還有
32 倍。另外三個的輸入由 `invntt_tomont` 的輸出算出，那是第 5 階段的 held-out 集合，界線不
該在這裡查。

---

### 第 4 階段：規模（陣列、迴圈、cut）

**目標**：§9.0 表中階段 4 的各列。

- Kyber `ntt` 預設每層一個 cut（`cuts.patch`）。另外提供變體 `cuts.half.patch`，每層每半一個 cut，
  讓顆粒度和 golden 一致，方便公平比較效能。顆粒度是 target 的事，核心沒有對應的旗標（G10）。
- Dilithium 的界線由規格模組依 `montgomery_reduce` 的輸出界推導，G4、G5 會檢查。

**驗收**

- **A4.1**：G2，含每個 cut 的快照。輸入是 10⁴ 筆亂數加極端樣式（全部 ±(q−1)、正負交錯）。
- **A4.2 數學層 golden**：
  - Kyber：每層的模數集合和 golden 相等（附錄 C.4 的腳本）；界線序列是 q, 2q, …, 8q；
    每層的 conjunct 數是 2, 4, …, 128。
  - P-256：每個 fiat 函式的後置條件形狀和對應的 OpenSSL golden 一致（`eqmodP1`、同一個模數 p、
    4 × 64-bit limb、相同的 Montgomery 因子）：

    | fiat-crypto | OpenSSL golden |
    |---|---|
    | `fiat_p256_mul` | `ecp_nistz256_mul_mont_{0,1}` |
    | `fiat_p256_sub` | `ecp_nistz256_sub_0`、`sub_v2_0` |
    | `fiat_p256_opp` | `ecp_nistz256_neg_0` |
    | `fiat_p256_to_montgomery` | `ecp_nistz256_to_mont_0` |
    | `fiat_p256_from_montgomery` | `ecp_nistz256_from_mont_0` |

    比對內容：模數、limb 權重、Montgomery 因子、前置條件的範圍（0 ≤ A < p）。
    `mul_by_3` 在 fiat 沒有對應函式，不比對。
- **A4.3**：G5、G6。Kyber `ntt` 與 fiat `p256_mul` 是**必過**的（兩者對應的 golden 都已知可解），
  兩種 hint 模式都用 `regression_76` 的 flag 組；其他目標要嘛 `unsat`，要嘛依 R6 做分類。
  時間與 MaxRSS 都要和 F6 對照。
- **A4.4**：G7，每個目標至少 20 個 C 突變，擊殺率 100%。
- **A4.5**：G1、G3、G4、G8、G9。
- **A4.6 效能預算**：每個目標的產生時間 ≤ 5 分鐘、記憶體 ≤ 8 GiB；每個 range VC 的 z3 時間 ≤ 10 分鐘
  （可以用 `--range-split`）。執行器的步數與耗時寫進報告。

**出口**：以上全部通過。

**實作進度（2026-09-24，尚未達到出口）**

目標八個（`target.toml` 標 `phase = 4`）：`kyber_ntt`（另有 `half` variant）、`dilithium_ntt`、
`fiat_p256_{mul,sub,opp,to_montgomery,from_montgomery}`、`fiat_25519_carry_mul`。zeta 表在
`params.py` 依定義重算（ζ = 17、1753，bit-reversal，Montgomery 形式），與上游表逐項相同，但規格不讀
上游的表。驗收腳本 `tests/phase4/accept.py`（`make accept-4`）。

這個階段逼出的核心改動，都是通用規則（G10 乾淨）：

1. **hint 判定的實作**（§6.4）：樣本過濾、cone 切片、逐步加深、批次；z3 用 `rlimit` 而不是
   `timeout`——timeout 在 bit-blast 大乘法器時不會被檢查（實測「2 秒」的查詢跑了幾分鐘），而且會隨
   機器負載變，G8 就不穩；rlimit 是決定性的。Kyber `ntt` 的 hint 從十分鐘以上變成數秒，兩次 build
   的 VC 位元組相同。
2. **range VC 拆分**（§7.4）：逐條義務、只帶 cone、以 `(reset)` 隔開；G5 要求每個回答都是 `unsat`。
   Kyber 一層合成一個檔 z3 超過 10 分鐘，拆開後 128 個檔全部 `unsat`。G1 對 range 檔只做語法檢查
   （拿掉 `check-sat` 再給 z3），不再重解一次。
3. **複製沿用 atom、同位拆分共用**（§6.3）。
4. **修正**：H2（全 1 的遮罩）在有號讀法下寫成 2ʷ − 1，實際是 −1——這條 hint 在 emit 模式會讓前提
   矛盾、VC vacuous 地 `unsat`。G3 過去只檢查 hint 的 BV 形式，所以沒抓到；現在 G3 也求值 hint 的
   代數形式與每條沿用恆等式。
5. `spec.py` 的 `build(variant=…)`、`target.toml` 的 `range_split`、`phase`（§4.1）。

目前結果（單次實測，機器與其他工作共用，時間只供參考）。第 0–3 階段的驗收在這些核心改動之後
全部重跑通過（`reports/accept-{0,1,2,3}-2026-09-24.md`）。

| 目標 | G5 | G6（emit） | 其他 |
|---|---|---|---|
| `kyber_ntt` | 128 檔全 `unsat` | 8/8 `unsat`，合計 246 s（沿用 atom 之前 484 s） | A4.2：七層模數集合與 golden 相等、界線 q…8q、conjunct 2…128；omit 模式 cut0 30 分鐘逾時（只記錄）；G8 位元組相同 |
| `kyber_ntt` `half` | — | 14/14 `unsat`，合計 164 s（golden 同顆粒度 185.19 s，F6） | 顆粒度與 golden 相同：第 1 層一刀，之後每層每半一刀 |
| `dilithium_ntt` | 一層 16 檔全 `unsat`（負載下 2253 s CPU） | 9/9 `unsat`，合計 907 s（最後一層、一次因式 279 s） | build 11 s，每層 128 個 H1 |
| `fiat_p256_mul` | 見下 | 30 分鐘逾時（原形、消去複製、沿用 atom 三種都是） | hint 找到 Montgomery 的四個低 limb = 0；build 230–277 s |
| `fiat_p256_sub`、`opp` | `unsat`（1.4 s、0.7 s） | `sub` 18 分鐘仍在搜尋（golden 不到 1 秒）；`opp` 3 s `sat`，G3、G4 通過，所以是沒證出來（F10） | A4.2 見下 |
| `fiat_p256_to/from_montgomery` | 見下 | `to` 10 分鐘逾時；`from` 183 s `sat` | hint 判定原本 1183 s，常數樣本過濾後 150 s |
| `fiat_25519_carry_mul` | 單檔 `unsat`（442 s） | 10 分鐘逾時 | build 20 s，不需要 hint |

A4.2（P-256）：把兩邊的後置條件當成關係比較（在隨機 limb 值上求值，要求 golden = 單位 × c2mix，
mod p）。`sub`、`sub_v2`、`neg`、`from_mont`、`mul_mont_1` 全部相符（單位 ±1）；`mul_mont_0` 的
後置條件講的是中途暫存器（golden 在最後的條件減法前切了一刀），只比對述詞與模數。前置條件的範圍，
除了 `to_mont` 都相同：golden 的 `to_mont` 沒有 A < p 的界，fiat 的前置條件有。

**兩個卡住 fiat 目標、需要決定的問題**

1. **G6：fiat 的 64 位元借位減法。** fiat 用 `signed __int128` 寫 `subborrowx`
   （`x1 = (arg2 − (int128)arg1) − arg3`）。§5.1 的有號性依序取自「產生它的運算」，第一個運算元是
   zext，所以這個減法被當成無號、判成 SPLIT，每個 limb 多出符號位橋接與 int1/uint1 轉換的 8 位元拆分；
   CryptoLine 的 `sbbs` 一個 limb 只有一條式子。bin/main 在這個形狀上跑不出來：連只有 118 條 IR 的
   `fiat_p256_sub` 都 18 分鐘沒結果，golden `sub` 不到 1 秒。bin/main 的 log 顯示 golden 走的是
   「代換全部 assignment 之後 eqmodP1 直接為真」，我們的檔留下約 55 條非 assignment 的式子，落到
   Z3 搜尋。可能的方向：有號性改用 debug info 的變數型別（§5.1 第 3 條目前排在運算之後），或對
   「兩種讀法之一恰好 EXACT」的加減法選那個讀法。兩者都動 §5.1/§6.2，需要先決定。
2. **G5：Montgomery 界。** `mul`、`to/from_montgomery` 的後置範圍 0 ≤ out < p 化約到最後條件減法前
   的 T < 2p，這要跨整個 256×256 乘法做算術推理，QF_BV bit-blast 做不到，區間分析也推不出（是關係
   性質）。同一件事在整數上很容易：z3 NIA 由恆等式 T·R = A·B + M·P 與輸入界 0.014 秒證出 T < 2p。
   一個做法是加一種 VC：在整數模型（代數敘述 + atom 的型別界 + range 前提）上證 range 目標，safety
   仍由 G5 在 BV 上證，避免循環。這會改 §8.2 的 soundness 論證，需要先決定。

---

### 第 5 階段：通用性（held-out）

**held-out 集合現在就凍結**。第 0–4 階段不准碰這些演算法，連規格都不准寫：

1. Kyber `invntt`（Gentleman–Sande butterfly、Barrett、tomont 因子）
2. Kyber `basemul`（mod x² − ζ 的乘積）
3. Dilithium `invntt_tomont`
4. fiat `p256_square`
5. fiat `curve25519_carry_square`

**驗收**

- **A5.1 核心凍結**：接入每個目標時只能寫 `targets/<t>/` 底下的檔案。
  `git diff --stat -- c2mix/ include/ runtime/` 必須是空的。
- **A5.2**：G1–G10 全部通過（G6 依 R6 處理）。fiat `p256_square` 另外和 OpenSSL
  `ecp_nistz256_sqr_mont_0` 做數學層比對（同 A4.2）。
- **A5.3**：如果真的需要改核心：
  1. 在報告裡寫下缺的是什麼能力。
  2. 以**通用規則**的形式實作（G10 會擋住方案特例）。
  3. 跑 `make accept-all` 回歸第 0–4 階段。
  4. 重新接入該目標，並在報告裡把它計為「需要改核心」。
- **通用性指標**：報告「不改核心就接入成功的數量 / 5」。

**出口**：5 個目標全部通過 G1–G10，並公布通用性指標。

---

### 第 6 階段：延伸（不在 v1 的驗收範圍）

- **SIMD**：支援 LLVM 向量型別（`<16 x i16>` 逐 lane 展開成純量）與一張 x86 intrinsic 語意表
  （例如 `llvm.x86.avx2.pmulh.w` → 逐 lane 的 L4′ 取高半）。先確認 LF5。
  驗證方式是比對執行器與 `-mavx2` 原生執行。
- **CBMC 第二前端**：把 CBMC `--smt2` 的輸出 lift 成同一種 c2mix IR 軌跡（附錄 E）。
  用途是更強的 G2：同一支 C 程式從兩條獨立路徑得到軌跡，在隨機輸入上逐 cut 比對快照。
- GF(2)[x] 代數（Classic McEliece）：`eqmod` 的模數用 2。
- 除以常數與取餘：拆成 x = q·d + rem，並加上 0 ≤ rem < d 的 range 義務。
- 自動選擇 cut 位置。

---

## 10. 專案結構與測試基礎設施

### 10.1 命令列

```
c2mix build <target> [--variant V] [-o out/]
            [--hints=emit|omit]            預設 omit
            [--int-encoding=alias|bv2int]  預設 alias（bv2int 只供 A/B）
            [--ghost=bind|inline|legacy-pow2]  預設 bind（legacy-pow2 只供 A/B）
            [--exactness=auto|split]       預設 auto
            [--carry=relevant|previous|all]    預設 relevant
            [--range-split=N]              預設為 target 的 range_split，否則 1
c2mix lint [--profile=strict|consumer] [--baseline FILE] FILES…
c2mix roundtrip FILES…
c2mix gate G<n> <target>
```

用 `bv2int` 或 `legacy-pow2` 產生的輸出，manifest 會標 `ab_only: true`，G3 與 G6 的結果不計入驗收。

### 10.2 目錄與設定

```
c2mix/                        獨立 repo
  c2mix/                      Python 套件（核心，G10 檢查範圍）
    cli.py
    frontend/{toolchain,llparse,execute,harness}.py
    ir/{ops,interp,intervals}.py
    lower/{rules,idioms,encode}.py
    spec/{dsl,check}.py
    lib/{poly,limbs,mont,ntt}.py
    vc/{assemble,carry,hints}.py
    emit/{mix,range,manifest}.py
    mixfmt/{reader,writer,lint}.py
    gates/{g1…g10}.py
  include/c2mix.h
  runtime/c2mix_rt.c          原生執行用的 runtime（G2）
  targets/<name>/{target.toml,cuts.patch,spec.py,params.py}
  vendor/                     上游原始碼，依 target.toml 的 commit 固定
  tests/phase0 … phase5/
  c2mix.toml
  Makefile                    make accept-0 … accept-5、accept-all、gate G=G2 T=kyber_ntt
```

`c2mix.toml`：

```toml
[toolchain]
clang    = "clang-18"
opt      = "opt-18"
llvm_as  = "llvm-as-18"
llvm_diff = "llvm-diff-18"
llvm_link = "llvm-link-18"

[solver.mix]
bin    = "../extend_z3/bin/main"      # extend_z3 是外部依賴，路徑可設定
memory = "15G"                        # 與 extend_z3/shs/run.sh 相同，用 systemd-run 限制
common = ["--minimal-fixed-watch", "--enable-eqmod-true-lemmas",
          "--enable-gb-preprocess", "--enable-ideal-rewrite"]
omit_extra = ["--enable-eq-gb-partition-prepass",
              "--eq-gb-partition-prepass-workers", "12"]   # 同 extend_z3/shs/regression_76.sh

[solver.range]
bin = "z3"
timeout_s = 600

[golden]
root = "../extend_z3/input"           # 只讀這兩個子目錄
sets = ["pqclean_kyber768_avx2_noAssume", "openssl/ecp_nistz256/x86_64"]
```

每次驗收都輸出 `reports/accept-<phase>-<date>.md`，內容是每個（目標 × 關卡）的 PASS/FAIL 表、
耗時與產物路徑。

### 10.3 工作規則

**W1 寫入範圍**：所有寫入都必須落在 `c2mix/` 專案目錄裡（`work/`、`out/`、`reports/`、
`vendor/`、`targets/` 等）。專案目錄以外的路徑一律**唯讀**，沒有例外——包含
`extend_z3/`（§2.1 的外部依賴）、系統目錄、家目錄，以及任何工具自己的暫存區。臨時檔放
`work/tmp/`（`make clean` 會清掉），不要用 `/tmp`。

這條的實作依據：`c2mix.toml` 裡的路徑都相對於專案根目錄解析（`config.Config.path`）；
`bin/main` 會把 `run.log` 寫進自己的工作目錄，所以 `oracle.run_mix` 替每次求解在 `log_dir`
底下開一個獨立的臨時目錄，絕不在 extend_z3 裡執行。

**W2 版本控制**：`git commit`、`git push`、`git init` 這類會改動版本歷史或推到遠端的指令
**不自動執行**，一律把指令列出來由人工執行。唯讀的查詢（`git status`、`git diff`、`git log`）
不受限制。

**W3 安裝**：不自動安裝套件。工具鏈缺東西時報告缺什麼（`Toolchain.missing()`），由人工安裝。

---

## 11. 風險

| # | 風險 | 緩解 |
|---|---|---|
| R1 | alias 編碼在 extend_z3 上變慢，或讓某些 prepass 失效 | A0.4 在寫任何核心程式碼之前就量測；保留 `bv2int` 模式做 A/B |
| R2 | LLVM 版本變動，文字 IR 格式改變 | 鎖定 LLVM 18；解析器只接受支援子集，遇到未知構造就失敗；A3.2 用 `llvm-as`/`llvm-diff` 驗證 round-trip |
| R3 | 256 係數規模的 range VC 在 z3 上太慢 | `--range-split`；每個 butterfly 的義務互相獨立 |
| R4 | 區間分析太鬆，把可以 EXACT 的運算判成 SPLIT，導致代數證明失敗 | 這只會讓證明失敗，不會 unsound。可選擇對失敗的運算再用 z3 補證 |
| R5 | 規格本身寫錯 | G4、S3、規格突變 |
| R6′ | flag 組合決定證不證得出來：同一個檔案有無 partition prepass 可能是 `sat` 與 0.24 s `unsat` 的差別（F10） | c2mix 自己的輸出預設帶 prepass flag（`c2mix.toml` 的 `prepass_default`）；manifest 記錄實際用的 flag |
| R6 | extend_z3 解不了新形狀的 VC（例如 L12 的非線性項 c·(a−b)，或 limb 解讀） | 這是研究發現，不是轉換器的錯。G6 不過時先分類：若 G3、G4、G5 都通過，**而且**同形狀的縮小版（例如 n = 8）是 `unsat`，就記為求解器限制並附上 `run.log`。`must_pass` 目標（Kyber `ntt`、fiat `p256_mul`）不適用這條豁免 |
| R7 | `-O0` 的 IR 很冗長（大量 load/store），執行器太慢 | `mem2reg` 先消掉純量的部分；執行器對常數運算即時摺疊；A4.6 設效能預算 |
| R8 | 輸入相依分支造成合流爆炸 | v1 只支援有直接後支配點、而且不含 cut 的分支，巢狀深度上限 8；超過就拒絕 |
| R9 | clang 本身的翻譯錯誤（信任基礎） | 鎖定版本；第 6 階段的 CBMC 第二前端可以提供獨立的交叉驗證 |

---

## 附錄 A：規則引理檔的格式

以 L4′（16-bit 有號同寬乘法，SPLIT）為例：

```smt
(set-logic ALL)
(declare-const a (_ BitVec 16)) (declare-const b (_ BitVec 16))
(declare-const H (_ BitVec 16)) (declare-const L (_ BitVec 16))
(assert (= H ((_ extract 31 16) (bvmul ((_ sign_extend 16) a) ((_ sign_extend 16) b)))))
(assert (= L ((_ extract 15 0)  (bvmul ((_ sign_extend 16) a) ((_ sign_extend 16) b)))))
(define-fun sa () Int (- (bv2nat a) (* 65536 (bv2nat ((_ extract 15 15) a)))))
(define-fun sb () Int (- (bv2nat b) (* 65536 (bv2nat ((_ extract 15 15) b)))))
(define-fun sH () Int (- (bv2nat H) (* 65536 (bv2nat ((_ extract 15 15) H)))))
(assert (not (= (+ (bv2nat L) (* sH 65536)) (* sa sb))))
(check-sat)          ; 預期 unsat
```

引理產生器對每個（規則 × 寬度 × 有號性 × 模式）產生一個這樣的檔案。A1.2 的突變版本則把其中
一項改掉，預期結果改為 `sat`。

**注意**：上面這個 16-bit 的例子本身 z3 4.8.12 跑不完（逾時 > 120 s，F9）。它仍然是格式的範例，
但實際驗收時混合式只跑 w = 4，其餘寬度改用 QF_BV 的像（A1.1）。

## 附錄 B：LLVM IR 支援子集

解析器接受的形式（LLVM 18、opaque pointer）：

| 項目 | 接受的形式 |
|---|---|
| 型別 | `i1`、`i8`、`i16`、`i32`、`i64`、`i128`、`ptr`、`[N x T]`、只含上述型別的 struct |
| 常數 | 整數常數、`zeroinitializer`、常數陣列、`constant` 全域的初始值 |
| 全域 | `@name = [internal] constant/global T init`；`constant` 的讀取直接摺疊 |
| 函式 | `define`（執行時 inline）、`declare`（只允許 runtime API 與白名單 intrinsic） |
| 指令 | §5.4 的表 |
| 指令旗標 | `nsw`、`nuw`、`exact`、`nneg`、`disjoint` 等會產生 poison 的旗標一律拒絕（`E-POISON-FLAG`，§5.5）；`inbounds` 忽略 |
| metadata | `!dbg`、`!DILocation`、`!DILocalVariable`、`!DIBasicType` 用於行號與型別；其他 metadata 忽略 |
| 屬性 | 函式與參數屬性忽略（它們不影響本子集的語意） |

A3.0 會統計實際目標用到的形式，並在必要時更新本表。

## 附錄 C：本規格依據的實測（重現指令）

以下指令都在 2026-09-22 實際跑過。C.1、C.2、C.5 是 CBMC 的實測，只和第二前端有關。

**C.1 CBMC 陣列展開**（F4）

```sh
cbmc l0.c --unwind 257 --max-field-sensitivity-array-size 256 --smt2 --outfile l0.smt2
# 256 個不同的 [[HEX]] 元素名；不加這個 flag 則退回 Array theory
```

**C.2 CBMC 常數表摺疊**（F4）：在 ntt 迴圈裡，`zeta!0@1#2` 被定義成 `(_ bv64778 16)`。

**C.3 `bv2int` 的有號性**（F3）

```sh
printf '(simplify (bv2int #xFFFF))\n' | z3 -in     # 輸出 65535
```

**C.4 模數樹比對**（F5、A4.2）

```python
import re
q = 3329; Rinv = pow(2**16, -1, q)
Z = [int(v) for v in re.findall(r'-?\d+', open('ntt.c').read()
                                  .split('zetas[128] = {')[1].split('};')[0])]
ref, k, L = {}, 1, 128
while L >= 2:
    for _ in range(0, 256, 2 * L):
        z = Z[k] * Rinv % q; k += 1
        ref.setdefault(L, set()).update({z, -z % q})
    L //= 2
MOD = re.compile(r'\(PConst 3329\) \(PSub \(PPow (?:\(PVar "x_0"\)|\(PConst \(bv2nat x_0\)\)) '
                 r'(\d+)\) \(PConst (\d+)\)\)')
gold = {}
for i in range(15):
    post = open(f'cut{i}.smt2').read().split('; postcondition')[1]
    for d, c in MOD.findall(post):
        gold.setdefault(int(d), set()).add(int(c))
assert all(ref[L] == gold[L] for L in ref)    # 2026-09-22：七層全部相等
```

**C.5 CBMC 的 `__int128`**（F4）：以 fiat-crypto `p256_64.c` 的 `fiat_p256_mul` 為目標跑 CBMC，
產生 168 處 `BitVec 128`、0 個 guard。

**C.6 apt 版本**（F8）

```sh
apt-cache policy clang llvm cbmc      # clang/llvm 候選 18，cbmc 候選 6.11.0
```

## 附錄 D：語料清單

**golden（確認正確，見 §2.1；路徑在 `extend_z3/input/` 下）**

| 目錄 | 檔數 | 基準（F6） |
|---|---:|---|
| `pqclean_kyber768_avx2_noAssume` | 15 | 185.19 s，需 partition prepass |
| `openssl/ecp_nistz256/x86_64` | 9 | 4.49 s |

**未確認（只作參考輸入，不作預期結果）**

| 目錄 | 檔數 | 可用於 |
|---|---:|---|
| `input/pqclean/kyber768/avx2` | 15 | lint 參考 |
| `input/saber/{assume,noassume}` | 34 | lint 參考 |
| `input/simple`、`input/others/redc` | 3 | lint 參考 |
| `working/cbmc_small` | 4 | C 測試程式來源；A3.5 的並列對照 |

## 附錄 E：CBMC 6.11 參考（第二前端用）

**必要參數**：`--unwind N --max-field-sensitivity-array-size 256 --smt2`。不加陣列參數時，
超過 64 元素的陣列會退回 Array theory。

**名稱文法**

```
|<scope>::<block…>::<name>!<thread>@<frame>#<ver>[[<HEX>]]|
```

| 例子 | 意義 |
|---|---|
| `main::1::r!0@1#2[[A0]]` | `main` 的區域陣列 `r`，元素 0xA0 = 160，版本 2 |
| `montgomery_reduce::1::t!0@2#3` | 第 2 次 inline 呼叫（`@2`）的區域變數 `t`，版本 3 |
| `montgomery_reduce::a!0@1#1` | 參數 `a` |
| `zetas#1` | 全域變數 |
| `goto_symex::return_value::f!0#1` | 函式 `f` 的回傳值 |
| `main::$tmp::return_value_nondet_int16!0@3#2` | nondet 輸入的轉接值 |
| `goto_symex::&92;guard#k` | 迴圈或分支的 guard |

lift 時的鍵是 `(scope, name, frame, ver, idx)`。frame 不能省略：同一個函式的多次 inline 呼叫
只靠 frame 區分。

**觀察到的行為**：對全域變數的賦值在輸出檔裡依程式順序出現（marker 的版本號夾在前後的陣列寫入之間）。
這是觀察，不是保證；第二前端若依賴它，必須先寫成測試。
