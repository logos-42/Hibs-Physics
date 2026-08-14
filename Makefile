# ProjectionPhysics 统一验证门禁
# canonical test command: make test  ⟹  python3 scripts/verify_all.py
.PHONY: test fast

test:
	python3 scripts/verify_all.py

fast:
	python3 scripts/verify_all.py --fast
