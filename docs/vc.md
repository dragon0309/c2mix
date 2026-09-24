# 從軌跡與規格到 VC

第 2 階段的產出。輸入是**軌跡**（trace）與**規格**（spec），輸出是每個 cut 兩個檔案加一個
manifest。第 3 階段會把 C 前端接在軌跡前面，這一層不用改。

```
trace + spec ──► S1–S4 自檢 ──► 切段 ──► 區間分析 ──► lowering ──► 事實攜帶 ──► hint ──► emit
```

## 軌跡（`c2mix/ir/trace.py`）

軌跡 = IR 程式 + **快照**。快照是規格能談論的時間點：entry、每次 `c2mix_cut(tag)`、exit
（§5.5）。每個快照把「已登記物件的每個元素」對到它當下的 SSA 值。

第 2 階段用 `TraceBuilder` 手寫軌跡；第 3 階段由執行器產生，介面相同。

## 規格 DSL（`c2mix/spec/dsl.py`）

`Target` 收集 pre / 每個 cut / post 的斷言。運算式是小型 AST，同一份規格會被用在三個地方：

| 用途 | 模組 |
|---|---|
| 在具體執行上求值（G3、G4） | `spec/evalspec.py`（一元多項式，§8.1 的判定方式） |
| 轉成 range 段的 BV 式 | `vc/terms.py::range_assert_bv`，寬度由區間分析決定 |
| 轉成 algebraic 段的 Poly 式 | `vc/terms.py::alg_assert_poly` |

`rng(lo <= e < hi)` 用得了鏈式比較：Python 會把它拆成兩個比較再 `and`，DSL 在 `__bool__`
裡把第一個比較記下來，`rng()` 再把兩半合起來。

## 切段與前提（`c2mix/vc/assemble.py`）

marker 把軌跡切成 S₀…S_K（§7.1）。每一段：

1. **區間分析**只走這一段的指令；起點是該 cut 的 range 斷言（§6.2）。只有「單一參照
   lo ≤ r[i] < hi」這種形狀能給出單一值的區間，其他（例如 limb 總和的界線）仍然會進 VC
   當前提，只是不影響 EXACT/SPLIT 判定。
2. **lowering** 只降這一段的指令。前面段落定義的值會被**宣告但不定義**——這正是它們成為
   本段輸入的方式。常數永遠內嵌（L1），所以不宣告。
3. **前提** = 該點的斷言 + 攜帶的事實；**目標** = 下一個點的斷言。

## 事實攜帶（`c2mix/vc/carry.py`）

SSA 值不會被改寫，所以先前證過的結論之後仍然成立。`relevant`（預設）只帶「提到本段讀到的值
或下一組斷言提到的值」的結論，ghost 參照不算。`previous` 帶前一個點，`all` 全帶。
soundness 只要求每個被帶的事實是某個較早 VC 的結論，這由 G9 從 manifest 檢查。

## hint（`c2mix/vc/hints.py`）

代數層看不到的 range 事實。候選：

| 代碼 | 內容 |
|---|---|
| H1 | L7 / L9′ / L9m / L11 的高低位等於常數（Montgomery 的 `lo = 0` 就是這個） |
| H2 | 遮罩全 0 或全 1 |
| H3 | 任何 1-bit 符號等於常數 |
| H4 | **兩個 1-bit 符號恆等**——條件減法的 select 條件就是它所選那個減法的借位 |
| H5 | **兩個 SPLIT 窄化丟掉的量相等**，⟦x⟧ − ⟦r⟧ = ⟦x′⟧ − ⟦r′⟧——兩次 wrap 互相抵銷 |
| H6 | **一個值等於它自己被拆出來的那些 1-bit 符號的加權和**，⟦v⟧ = Σ 2ⁱ⟦bᵢ⟧ |

每個候選都要 z3 在該段的 range 模型上證出來才會採用；range VC 會再獨立驗一次（G5）。

三條都是被實際目標逼出來的：

- H4（第 2 階段）：沒有它，T2b 的條件減法在代數層缺少「條件 = 借位」這條連結，
  `bin/main` 給出 `sat`；加上之後 0.24 秒 `unsat`。
- H5（第 3 階段）：Barrett 約簡的 `t *= q` 在 int16 wrap 一次，`a - t` 又 wrap 回來，
  同餘式只因為兩次抵銷才成立。CryptoLine 的 `.cl` 是人工寫下這條；這裡由 z3 判定。
- H6（第 3 階段）：位元運算與比較在代數層是自由的（L13），所以「把乘數一位一位拆開再
  累加」的程式，代數層沒有任何東西把值和它的位元連起來。

**只替證出來的候選要 atom。** 在證明之前就跟 encoder 要 atom，會替最後被丟掉的候選留下
alias 與 L10 橋接，等於憑空多出未知數。`cbmc04_loop_mul` 因此多了 8 個橋接與 8 個 1-bit
符號，`bin/main` 從 0.13 秒變成 10 分鐘以上跑不完。同理，H6 找到的分解若是另一條的後綴
（同一個值的移位副本），也要丟掉——移位自己的拆解式已經說了同一件事。

## 兩個輸出檔

| 檔案 | 前提 | 程式 | 目標 |
|---|---|---|---|
| `cutN.smt2`（§7.3） | Rᵢ、Aᵢ、攜帶的事實 | BV(Sᵢ)、ALG(Sᵢ) | ¬Aᵢ₊₁ |
| `cutN.range.smt2`（§7.4） | Rᵢ、攜帶的 range 事實 | BV(Sᵢ) | ¬(Rᵢ₊₁ ∧ safety ∧ hints) |

`--hints=emit` 會把 hint 寫進兩邊（mix 檔的 range 段放 `(assert true)` 佔位、algebraic 段放
等式；range VC 放義務）；`--hints=omit` 只記在 manifest。

## 關卡

| 關卡 | 模組 | 判定 |
|---|---|---|
| G3 軌跡一致 | `gates/g3.py` | 真實執行是每個 VC 前提的模型（抓 vacuity） |
| G4 規格成立 | `gates/g4.py` | 規格本身在真實執行上為真 |
| G5 range 義務 | `gates/g5.py` | 每個 range VC 用 z3 求解為 `unsat` |
| G6 代數目標 | `gates/g6.py` | 每個 mix VC 用 `bin/main` 求解為 `unsat` |
| G7 突變 | `gates/g7.py` | 每個突變都要被某個關卡擋下 |
| G8 決定性 | `gates/g8.py` | 兩次建置位元組相同 |
| G9 cut 鏈 | `gates/g9.py` | 每個被攜帶的事實都有更早的來源 |

### `bin/main` 的 `sat` 不是反例

同一個 T2b 檔案：不加 partition prepass 是 `sat`（128 秒），加了之後 0.24 秒 `unsat`。
所以 `sat` 只表示「沒證出來」。真正錯的 VC（把 T2c 的模數改成 q+1）兩種設定都是 `sat`。
G6 因此只認 `unsat`，遇到 `sat` 要先用 G3、G4 分類，這也是 spec R6 的處理方式。
c2mix 自己的輸出預設帶 prepass flag（`c2mix.toml` 的 `prepass_default`）。

### 突變不該是等價的

G7 不會突變「沒有人讀的值」：沒被任何指令讀、也沒出現在規格參照裡的常數或陣列元素，
改了也不會有任何關卡看得出來，那不是漏網而是等價突變。索引突變因此限定在規格真的讀到的
`(時間點, 物件, 索引)` 上。
