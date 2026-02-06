def check(G, **kwargs):
    """
    Check whether G is a forest (acyclic).

    A graph is a forest if it contains no cycle.

    Optional counter-certificate:
        forest_cycle: list of vertices forming a cycle in G.

    Parameters
    ----------
    G : sage.graphs.graph.Graph
    **kwargs : dict

    Returns
    -------
    bool
    """
    counter = kwargs.get("forest_cycle")
    if counter is not None:
        # Verify cycle counter-certificate
        cycle = counter
        if len(cycle) < 3:
            raise ValueError(
                f"Counter-certificate invalid: cycle has length {len(cycle)} < 3"
            )
        for i in range(len(cycle)):
            u, v = cycle[i], cycle[(i + 1) % len(cycle)]
            if not G.has_edge(u, v):
                raise ValueError(
                    f"Counter-certificate invalid: no edge {u}-{v}"
                )
        return False

    return G.is_forest()
