def check(G, **kwargs):
    """
    Check whether G is a forest (acyclic).

    A graph is a forest if it contains no cycle.
    No certificates — the standard algorithm is O(V+E).

    Parameters
    ----------
    G : sage.graphs.graph.Graph
    **kwargs : dict (ignored)

    Returns
    -------
    bool
    """
    return G.is_forest()
