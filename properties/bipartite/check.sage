# Verification mode:
#   "generic"    — standard algorithm, no certificates needed
#   "certified"  — requires certificates in witness data
#   "both"       — has generic + certified; --cross-check compares them
CERTIFICATE_MODE = "both"

def check(G, **kwargs):
    """
    Check whether G is bipartite.

    A graph is bipartite if its vertex set admits a 2-coloring with no
    monochromatic edges. Equivalently, it contains no odd cycle.

    Certificate (for TRUE):
        bipartite_coloring: dict mapping vertices to 0 or 1.
    Counter-certificate (for FALSE):
        bipartite_odd_cycle: list of distinct vertices forming an odd cycle.

    If certificates are provided, validates them and returns the certified
    result. If not, falls back to the generic algorithm.

    Parameters
    ----------
    G : sage.graphs.graph.Graph
    **kwargs : dict

    Returns
    -------
    bool
    """
    cert = kwargs.get("bipartite_coloring")
    counter = kwargs.get("bipartite_odd_cycle")
    if cert is not None and counter is not None:
        raise ValueError("Cannot provide both certificate and counter-certificate")

    if cert is not None:
        # Verify 2-coloring certificate
        verts = set(G.vertices())
        colored = set()
        for v, c in cert.items():
            if c not in (0, 1):
                raise ValueError(
                    f"Certificate invalid: vertex {v} has color {c}, expected 0 or 1"
                )
            colored.add(v)
        missing = verts - colored
        if missing:
            raise ValueError(
                f"Certificate invalid: vertices {missing} have no color assignment"
            )
        for u, v, _ in G.edges():
            if cert[u] == cert[v]:
                raise ValueError(
                    f"Certificate invalid: edge {u}-{v} has same color {cert[u]}"
                )
        return True

    if counter is not None:
        # Verify odd cycle counter-certificate: simple cycle of odd length
        cycle = counter
        if len(cycle) < 3:
            raise ValueError(
                f"Counter-certificate invalid: cycle has length {len(cycle)} < 3"
            )
        if len(cycle) % 2 == 0:
            raise ValueError(
                f"Counter-certificate invalid: cycle has even length {len(cycle)}"
            )
        if len(set(cycle)) != len(cycle):
            raise ValueError(
                "Counter-certificate invalid: cycle has repeated vertices"
            )
        for i in range(len(cycle)):
            u, v = cycle[i], cycle[(i + 1) % len(cycle)]
            if not G.has_edge(u, v):
                raise ValueError(
                    f"Counter-certificate invalid: no edge {u}-{v}"
                )
        return False

    # No certificates provided — fall back to generic
    return G.is_bipartite()


def check_no_certs(G):
    """Generic algorithm, ignoring all certificates. Used for cross-checking."""
    return G.is_bipartite()
