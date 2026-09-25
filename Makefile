PY ?= python3
GOLDEN_ROOT := ../extend_z3/input
GOLDEN := $(GOLDEN_ROOT)/pqclean_kyber768_avx2_noAssume $(GOLDEN_ROOT)/openssl/ecp_nistz256/x86_64

.PHONY: test accept-0 accept-1 accept-2 accept-3 accept-4 accept-all ab-0 lemmas fuzz lint-golden baseline-0 negative-0 g10 clean

test:                       ## unit tests (fast, no bin/main)
	$(PY) -m unittest discover -s tests -t .

accept-0:                   ## phase 0 gates A0.1–A0.3 + G10 -> reports/accept-0-<date>.md
	$(PY) tests/phase0/accept.py

accept-1:                   ## phase 1 gates A1.1–A1.5 + G10 -> reports/accept-1-<date>.md
	$(PY) tests/phase1/accept.py

accept-2:                   ## phase 2 gates A2.1–A2.5 + G10 -> reports/accept-2-<date>.md
	$(PY) tests/phase2/accept.py

accept-3:                   ## phase 3 gates A3.0–A3.9 + G10 -> reports/accept-3-<date>.md
	$(PY) tests/phase3/accept.py

accept-4:                   ## phase 4 gates A4.1–A4.6 + G10 -> reports/accept-4-<date>.md (hours)
	$(PY) tests/phase4/accept.py

accept-all: accept-0 accept-1 accept-2 accept-3   ## regression rule (§9): every completed phase

ab-0:                       ## A0.4 encoding A/B (slow: runs bin/main ~40 times)
	$(PY) tests/phase0/ab_encoding.py --ghost-bv2int

lemmas:                     ## write the rule lemmas to work/lemmas and check them
	$(PY) -m c2mix lemmas --out work/lemmas --mutants --check --jobs 12

fuzz:                       ## A1.3/A1.4 only
	$(PY) tests/phase1/fuzz.py

lint-golden:
	$(PY) -m c2mix lint --profile=consumer --z3 -q --baseline tests/phase0/lint-baseline.json $(GOLDEN)

baseline-0:                 ## rewrite the A0.1 baseline (review the diff before keeping it)
	$(PY) -m c2mix lint --profile=consumer --z3 -q --write-baseline tests/phase0/lint-baseline.json $(GOLDEN)

negative-0:                 ## regenerate the A0.3 negative corpus
	$(PY) tests/phase0/make_negative.py

build-%:                    ## c2mix build <target>, e.g. make build-kyber_montgomery
	$(PY) -m c2mix build $* --hints=emit

g10:
	@! grep -riEn 'kyber|dilithium|saber|mceliece|p256|25519|3329|8380417' c2mix/ include/ runtime/ --exclude-dir=__pycache__

clean:
	rm -rf work/phase0 work/phase3 work/phase4 work/tmp work/build work/gate
	find . -name __pycache__ -type d -exec rm -rf {} +
