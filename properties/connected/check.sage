def check(G, **kwargs):
    """
    Check whether G is connected.

    A graph is connected if it has exactly one connected component.

    Optional counter-certificate:
        connected_components: list of two vertex sets in different components.

    Parameters
    ----------
    G : sage.graphs.graph.Graph
    **kwargs : dict

    Returns
    -------
    bool
    """
    cert = kwargs.get("connected_components")
    if cert is not None:
        # Verify counter-certificate: two vertex sets should be in different components
        comp1, comp2 = cert
        # Check that no edge crosses between the two sets
        for u in comp1:
            for v in comp2:
                if G.has_edge(u, v):
                    raise ValueError(
                        f"Counter-certificate invalid: edge {u}-{v} crosses components"
                    )
        # Check that at least one vertex from each set exists in G
        if not all(v in G for v in comp1) or not all(v in G for v in comp2):
            raise ValueError("Counter-certificate contains vertices not in G")
        return False
    return G.is_connected()
