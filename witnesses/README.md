# Witness Files

Each YAML file in this directory witnesses a **realized cell** — a combination of
property values that is simultaneously achievable by some finite simple graph.

## YAML Schema

```yaml
description: "Human-readable name/description of the graph"

graph:
  format: edge_list | graph6 | sparse6
  vertices: <int>          # required for edge_list
  data: <edges or string>  # [[0,1],[1,2]] for edge_list; encoded string otherwise

properties:
  <property_id>: true | false   # one entry per property in the registry

certificates:                   # optional: proof data for TRUE properties
  <cert_key>: <cert_data>

counter_certificates:           # optional: proof data for FALSE properties
  <counter_cert_key>: <data>

provenance:                     # optional metadata
  source: "where the graph comes from"
  url: "reference URL"
  found_by: "manual | automated | literature"
```

## Requirements

- The graph must have at least `MIN_VERT` (currently 3) vertices.
- The `properties` dict must list **every** property in `properties/registry.yaml`.
- Declared values must match what the SageMath checkers compute.
- A witness must not provide both a certificate and counter-certificate for the same property.

## Graph Formats

| Format | `data` field |
|--------|-------------|
| `edge_list` | List of `[u, v]` pairs. Requires `vertices` field. No self-loops or duplicates. |
| `graph6` | Standard graph6 encoded string (e.g., `"Dhc"`). |
| `sparse6` | Standard sparse6 encoded string (starts with `:`). |

## Filenames

Freeform descriptive snake_case: `petersen.yaml`, `cycle_5.yaml`, `paley_13.yaml`.

## Canonical Witnesses

For each realized cell, the **canonical witness** is the one with the smallest graph
(by vertex count, with edge count as tiebreaker). Smaller graphs are preferred.

## See Also

- `DESIGN_SPEC.md` §5.4 for the full specification
- `gallery/` for additional notable examples (looser merge policy)
