def check(G, **kwargs):
    """
    Check whether G is bipartite.

    A graph is bipartite if its vertex set admits a 2-coloring with no
    monochromatic edges. Equivalently, it contains no odd cycle.

    Optional certificate:
        bipartite_coloring: dict mapping vertices to 0 or 1.
    Optional counter-certificate:
        bipartite_odd_cycle: list of vertices forming an odd cycle.

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
        for u, v, _ in G.edges():
            if cert[u] == cert[v]:
                raise ValueError(
                    f"Certificate invalid: edge {u}-{v} has same color {cert[u]}"
                )
        return True

    if counter is not None:
        # Verify odd cycle counter-certificate
        cycle = counter
        if len(cycle) % 2 == 0:
            raise ValueError(
                f"Counter-certificate invalid: cycle has even length {len(cycle)}"
            )
        for i in range(len(cycle)):
            u, v = cycle[i], cycle[(i + 1) % len(cycle)]
            if not G.has_edge(u, v):
                raise ValueError(
                    f"Counter-certificate invalid: no edge {u}-{v}"
                )
        return False

    return G.is_bipartite()
