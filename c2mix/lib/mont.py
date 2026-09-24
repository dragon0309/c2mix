"""Montgomery parameters (spec §4.3, `lib.mont`). No scheme constants here (G10)."""
from __future__ import annotations

from dataclasses import dataclass


@dataclass(frozen=True)
class Montgomery:
    q: int
    bits: int                 # R = 2^bits

    @property
    def R(self) -> int:
        return 1 << self.bits

    @property
    def r_mod_q(self) -> int:
        return self.R % self.q

    @property
    def r_inv(self) -> int:
        """R⁻¹ mod q."""
        return pow(self.R, -1, self.q)

    @property
    def q_inv(self) -> int:
        """q⁻¹ mod R — what the reduction multiplies the low half by."""
        return pow(self.q, -1, self.R)

    @property
    def q_inv_neg(self) -> int:
        """−q⁻¹ mod R, the other convention."""
        return (-self.q_inv) % self.R

    def to_montgomery(self, x: int) -> int:
        return x * self.R % self.q

    def from_montgomery(self, x: int) -> int:
        return x * self.r_inv % self.q

    def signed(self, v: int) -> int:
        """v as a signed value of `bits` bits, which is how C writes these constants."""
        v %= self.R
        return v - self.R if v >= self.R // 2 else v

    def signed_q_inv(self) -> int:
        return self.signed(self.q_inv)
