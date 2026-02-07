CERTIFICATE_MODE = "generic"

def check(G, **kwargs):
    """Check whether G is triangle-free (contains no K_3 subgraph)."""
    return G.is_triangle_free()
