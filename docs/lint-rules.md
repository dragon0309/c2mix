# c2mix lint 規則

`c2mix lint` 檢查 mix 檔（spec §7.3）是否符合格式契約。實作在 `c2mix/mixfmt/lint.py`，
規則表 `RULES` 與本文件必須同步。

```
c2mix lint [--profile=strict|consumer] [--baseline FILE] [--write-baseline FILE] [--z3] [-q] FILES|DIRS…
```

- 訊息格式：`<檔案>:<行>: <E|W>-<代碼> <說明>`。嚴重度前綴依 profile 決定，代碼本身不變。
- 結束碼：有任何 error，或指定 `--baseline` 而 warning 不一致時，回傳 1。
- `--z3`：另外用 z3 解析檔案（規則 PARSE）。解析方式與 extend_z3 完全相同：在第一個
  `(set-logic` 所在行之後插入 prelude，只拿掉 `(check-sat)`，不求解。

## profile

| profile | 用途 | 嚴重度 |
|---|---|---|
| `strict` | c2mix 自己的輸出（G1） | 除 TRIVIAL-GOAL（M6 允許，永遠是 warning）外全部是 error |
| `consumer` | golden 與其他外部語料（A0.1） | 只有「extend_z3 讀不進來或會讀錯」的規則是 error，其餘降為 warning |

## 規則

| 代碼 | 依據 | consumer | strict | 檢查內容 |
|---|---|---|---|---|
| SET-LOGIC | M1 | E | E | 恰好一個 `(set-logic ALL)`；它在任何宣告與 assert 之前；原始文字中第一個含 `(set-logic` 的行，內容恰好是 `(set-logic ALL)`（extend_z3 在這一行之後插入 prelude） |
| POLY-DECL | M2 | E | E | 不得有 `declare-datatype(s)`、`declare-sort`、`define-sort`，不得重新宣告 `Poly`、`eqP`、`eqmodP1..4` 或 Poly 建構子。另外檢查原始文字：只要出現 `(declare-datatype Poly`，或同時出現 `(declare-datatypes` 與 `Poly`（即使在註解裡），extend_z3 就不會插入 prelude |
| POLY-SORT | M3 | E | E | 宣告裡的 Poly sort 只能是 `(Poly Int)` |
| PRED | M3 | E | E | 判斷式只用 `eqP`/`eqmodP1`/`eqmodP2`，引數個數正確（`eqmodP3`/`eqmodP4` 只有宣告、沒有編譯後的處理）；Poly 建構子引數個數正確 |
| PVAR | M4 | E | E | `PVar` 的引數必須是字串字面值 |
| INDET-BV | M4 | W | E | 不定元被編成 1-bit bit-vector：`(PPow (PConst (bv2nat v)) k)`，v 是 `(_ BitVec 1)`、k ≥ 2。1-bit 的值滿足 vᵏ = v，模數理想會退化（D5）。每個符號報一次，位置在它的宣告 |
| BV2INT | M5 | W | E | 用了 `bv2int`。Z3 把它當無號（F3），有號值應改用 alias `s__v`。每個指令報一次 |
| PCONST-ATOM | M5 | W | E | `PConst` 的引數不是原子：數字、`(- n)`、`(bv2nat v)`、宣告為 Int 的符號（alias）。`(bv2int v)` 歸 BV2INT，不在這裡重複報 |
| GOAL | M6 | E | E | postcondition 段恰好一個指令，形如 `(assert (not …))` |
| TRIVIAL-GOAL | M6 | W | W | 目標平凡為真（`true` 或只由 `true` 組成的 `and`）。M6 允許，但要求寫成 `(assert (not (and true true)))`；寫法不同時訊息會註明 |
| SYMBOL | M7 | W | E | 宣告的符號符合 `[A-Za-z_][A-Za-z0-9_]*`；不得使用 `\|…\|`。命名規則（`r_017_3` 等）需要 manifest 才能判斷，不在 lint 範圍 |
| CONST-FORMAT | M8 | W | E | `(_ bvN w)` 字面值；寬度為 4 的倍數卻寫 `#b`；數字有前導零；小數；負數寫成 `-5`（應為 `(- 5)`） |
| SECTIONS | M10 | E | E | 五行 section 註解各出現一次、順序正確、字面完全相同（含 range 那行的尾端空白）。這條不過時，依賴分段的規則（GOAL、TRIVIAL-GOAL、LAYOUT、DECL-ORDER、ALIAS）不執行 |
| DECL | consumer | E | E | 每個用到的符號都有宣告，而且只宣告一次（`let`/`forall`/`exists` 綁定的名稱除外） |
| DECL-ORDER | §7.3 | W | E | declaration 段依名稱排序（Python 字串順序）。每個檔案報一次，位置在第一個亂序處 |
| LAYOUT | §7.3 | W | E | 檔頭恰好是 `(set-info :smt-lib-version 2.0)` 加 set-logic；declaration 段只有 `declare-const`；range 與 algebraic 段只有 `assert`；range 段不含 Poly 項；目標寫成 `(not (and …))`；check 段恰好是 `(check-sat)` `(exit)`；除五行 section 註解外沒有其他註解（包括指令內的註解） |
| ALIAS | §6.1 | W | E | 每個 Int 符號 `s__v`（v 是宣告過的 w-bit BV）恰好有一條定義 `(= s__v (- (bv2nat v) (* 2^w (bv2nat ((_ extract w-1 w-1) v)))))`，而且放在 range 段。放置位置的細節（緊接在 BV 定義之後）要等 emit 層有 SSA 資訊才檢查 |
| PARSE | consumer | E | E | 只在 `--z3` 時執行：z3 以 extend_z3 的方式解析檔案沒有錯誤（抓 sort 錯誤等靜態規則看不到的問題）。s-expression 本身不平衡時，不論有沒有 `--z3` 都以 PARSE 回報 |

M9（決定性）無法從單一檔案判斷，由 G8 檢查。

計數單位：同一個指令（行）上同一條規則只報一次。DECL 的未宣告符號、INDET-BV 以符號為單位；
DECL-ORDER 以檔案為單位。baseline 比對的是每個檔案各 warning 代碼的次數。

## baseline

`tests/phase0/lint-baseline.json` 記錄兩組 golden 在 `consumer` profile 下的 warning 次數，
鍵是相對於 `c2mix.toml` `[golden].root` 的路徑。更新方式是 `make baseline-0`，更新後要人工檢查 diff 才能保留。

2026-09-22 的內容：

| golden | warning |
|---|---|
| Kyber noAssume（15 檔） | W-BV2INT（全部）、W-DECL-ORDER（全部）、W-INDET-BV（cut1–14，`x_0` 是 `(_ BitVec 1)`）、W-TRIVIAL-GOAL（cut7、cut14） |
| OpenSSL（9 檔） | W-DECL-ORDER（全部）、W-LAYOUT（全部：目標是 `(not (eqmodP1 …))`，沒有包 `and`） |

與 spec A0.1 列出的預期 warning 一致；OpenSSL 的 W-LAYOUT 屬於「其餘降級規則」。

## 負面語料（A0.3）

`tests/phase0/negative/<代碼>.smt2`：以 `tests/phase0/clean/minimal.smt2`（strict 下 0 診斷、
z3 可解析、bin/main 為 `unsat`）為底，每檔只改一處，只觸發該代碼。由 `tests/phase0/make_negative.py`
產生，`tests/phase0/test_negative.py` 檢查。唯一的例外是加 `--z3` 時，DECL 檔同時觸發 PARSE
（z3 本身也拒絕未宣告的符號）。
