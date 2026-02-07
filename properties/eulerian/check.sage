CERTIFICATE_MODE = "generic"

def check(G, **kwargs):
    """
    Check whether G is Eulerian (admits an Euler circuit).

    A graph is Eulerian iff it has no edges, or it is connected and every
    vertex has even degree.
    """
    if G.size() == 0:
        return True
    if not G.is_connected():
        return False
    return all(G.degree(v) % 2 == 0 for v in G.vertices())
