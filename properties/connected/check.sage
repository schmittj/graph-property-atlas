def check(G, **kwargs):
    """
    Check whether G is connected.

    A graph is connected if it has exactly one connected component.
    No certificates — the standard algorithm is O(V+E).

    Parameters
    ----------
    G : sage.graphs.graph.Graph
    **kwargs : dict (ignored)

    Returns
    -------
    bool
    """
    return G.is_connected()
