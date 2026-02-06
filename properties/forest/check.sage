# Verification mode:
#   "generic"    — standard algorithm, no certificates needed
#   "certified"  — requires certificates in witness data
#   "both"       — has generic + certified; --cross-check compares them
CERTIFICATE_MODE = "generic"

def check(G, **kwargs):
    """
    Check whether G is a forest (acyclic).

    A graph is a forest if it contains no cycle.
    Standard algorithm is O(V+E), no certificates needed.

    Parameters
    ----------
    G : sage.graphs.graph.Graph
    **kwargs : dict (ignored)

    Returns
    -------
    bool
    """
    return G.is_forest()
