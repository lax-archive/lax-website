`Fields.ilean.json` is Lean 4.30.0's reference output for `Lax17/Fields.lean`,
kept as a test fixture so CI needs neither Lean nor network access. Refresh
from this directory with:

```sh
lean -R . -i /tmp/Fields.ilean Lax17/Fields.lean
cp /tmp/Fields.ilean Fields.ilean.json
```

It covers record keys and updates, type-directed projections with colliding
field names, `open`, `export`, private globals, generated and inductive
constructors, shadowing, Unicode positions, and escaped identifier labels.
