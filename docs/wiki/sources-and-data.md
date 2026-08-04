---
title: 资料与数据
source: session
last_confirmed: 2026-08-04
audience: self
stage: draft
schema_version: 2
created: 2026-08-04
tags: [data, raw]
status: current
---

原始资料默认放在本地 raw 根目录，不直接进 Git。

raw 根目录建议：

```text
../hibs_physics_raw/
```

GitHub 里只保留 manifest 和编译结果。

少量 raw 可以手工登记；新文件一多，直接跑：

```bash
python3 scripts/ingest_raw.py
python3 scripts/stale_report.py
python3 scripts/delta_compile.py --write-drafts
```

前者把本地 raw 编成 manifest + lock + intake report，第二个告诉你哪些 wiki 页面已经 stale，第三个只生成手动草稿，不会偷偷覆盖现有 wiki。
