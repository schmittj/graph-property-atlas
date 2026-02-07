CERTIFICATE_MODE = "both"

def check(G, **kwargs):
    """
    Check whether G is Hamiltonian (has a Hamiltonian cycle).

    Certificate (for TRUE):
      hamiltonian_cycle: list of vertices forming a Hamiltonian cycle.
    """
    cycle = kwargs.get("hamiltonian_cycle")
    if cycle is not None:
        return _check_hamiltonian_cycle(G, cycle)
    return G.is_hamiltonian()

def _check_hamiltonian_cycle(G, cycle):
    """Verify that cycle is a valid Hamiltonian cycle in G."""
    n = G.order()
    if len(cycle) != n:
        return False
    if set(cycle) != set(G.vertices()):
        return False
    for i in range(n):
        u, v = cycle[i], cycle[(i + 1) % n]
        if not G.has_edge(u, v):
            return False
    return True
