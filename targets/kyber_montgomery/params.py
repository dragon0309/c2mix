"""Kyber constants. Scheme knowledge lives here, never in the core (G10)."""
Q = 3329                    # KYBER_Q
R = 1 << 16                 # the Montgomery radix
HALF = (Q - 1) // 2
MONT_BOUND = Q * (1 << 15)  # montgomery_reduce's stated input bound
