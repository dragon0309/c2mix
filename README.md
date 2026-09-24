# c2mix

C → SMT2（CryptoLine mix 格式）轉換器。規格見 [spec.md](spec.md)。

目前進度：第 0 階段（格式層）、第 1 階段（IR 與雙模型 lowering）、第 2 階段（規格 DSL 與
VC 組裝）、第 3 階段（LLVM 前端：解析器、執行器、13 個純量目標）。

```sh
python3 -m c2mix build <target> [--hints=emit] [-o DIR]   # C 原始碼 → out/<target>/
python3 -m c2mix gate G2 <target>                         # 單獨跑一道關卡
python3 -m c2mix lint --profile=consumer FILES…   # 格式契約檢查（docs/lint-rules.md）
python3 -m c2mix roundtrip [-o DIR] [--solve] FILES…
python3 -m c2mix lemmas --out DIR --mutants --check   # 規則引理（docs/lemmas.md）

make test        # 單元測試（約 10 秒）
make accept-0    # 第 0 階段驗收 → reports/accept-0-<date>.md（會跑 bin/main，約 4 分鐘）
make accept-1    # 第 1 階段驗收 → reports/accept-1-<date>.md（約 10 分鐘）
make accept-2    # 第 2 階段驗收 → reports/accept-2-<date>.md（約 2 分鐘）
make accept-3    # 第 3 階段驗收 → reports/accept-3-<date>.md（約 15 分鐘）
make accept-all  # 四個階段都跑（§9 的回歸規則）
make ab-0        # A0.4 編碼 A/B → reports/a0.4-<date>.md（約 10 分鐘）
make fuzz        # 只跑 A1.3/A1.4 的隨機測試
```

## 結構

| 目錄 | 內容 |
|---|---|
| `c2mix/frontend/` | clang/opt 驅動（`toolchain`）、LLVM IR 子集解析器（`llparse`）、執行器（`execute`）、harness 產生器（`harness`） |
| `c2mix/mixfmt/` | mix 檔的 reader、writer、lint、extend_z3 的 prelude 副本 |
| `c2mix/ir/` | c2mix IR（`ops`）、直譯器（`interp`）、區間分析與 EXACT/SPLIT 判定（`intervals`） |
| `c2mix/lower/` | 整數編碼（`encode`）、規則 L1–L14（`rules`）、引理產生器（`lemmas`）、敘述求值（`evaluate`） |
| `c2mix/spec/` | 規格 DSL（`dsl`）、自檢 S1–S4（`check`）、在執行上求值（`evalspec`） |
| `c2mix/lib/` | 通用解讀：`poly`、`limbs`、`mont`、`ntt`（不含任何方案常數） |
| `c2mix/vc/`, `c2mix/emit/` | 切段與前提（`assemble`）、事實攜帶（`carry`）、hint（`hints`）、輸出檔（`emit/*`） |
| `c2mix/gates/` | G1–G9 |
| `targets/` | 每個目標的 `target.toml`、`spec.py`、`params.py`、`cuts.patch`（方案知識只能在這裡） |
| `vendor/` | 上游原始碼，commit 固定在 `target.toml` |
| `include/`, `runtime/` | `c2mix.h` 與原生執行用的 runtime（G2） |
| `c2mix/` | `cli`、`config`、`oracle`（呼叫 bin/main 與 z3） |
| `tests/phase0/` … `tests/phase3/` | 各階段的單元測試、驗收腳本與實驗；`tests/phase3/reject`、`tests/phase3/robust` 是 A3.7、A3.8 的語料 |
| `docs/` | [lint-rules.md](docs/lint-rules.md)、[lemmas.md](docs/lemmas.md)、[vc.md](docs/vc.md) |

需求：Python 3.12（只用標準函式庫）、clang/llvm 18、z3、extend_z3 的 `bin/main`
（路徑在 `c2mix.toml`）。
c2mix 只讀取 extend_z3；bin/main 在 `work/` 底下的獨立目錄執行，它寫的 `run.log` 不會落在 extend_z3 裡。
