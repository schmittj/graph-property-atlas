# Gallery

Additional notable graph examples beyond the canonical witnesses.

Same YAML schema as `witnesses/`. Multiple gallery files per cell are allowed.

## Merge Criteria

Gallery entries should be **notable** — tagged with at least one of:

| Tag | Meaning |
|-----|---------|
| `named` | A named graph (Petersen, Heawood, etc.) |
| `extremal` | Extremal for some property |
| `smallest` | Was previously the canonical witness (demoted by a smaller one) |
| `counterexample` | Historically significant counterexample |
| `historical` | Historically important |

## Example

```yaml
description: "Petersen graph"

graph:
  format: graph6
  data: "IsP@OKWHo"

properties:
  connected: true
  bipartite: false
  # ... all properties

tags:
  - named

provenance:
  source: "Classical named graph"
```
