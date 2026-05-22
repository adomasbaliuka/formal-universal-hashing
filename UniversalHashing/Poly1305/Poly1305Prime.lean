import Mathlib
import PrimeCert

/-!
# Primality of 2^130 - 5

Proved via Lucas primality certificates.
-/

namespace Poly1305Prime

def P : ℕ := 2 ^ 130 - 5

theorem prime_two_pow_130_sub_5 :
    Nat.Prime 1361129467683753853853498429727072845819 := prime_cert%
  [small {3; 5; 17; 23; 73; 487},
   pock3 (32985101, 2, 1, 3, 2 ^ 2 * 5 ^ 2 * 17),
   pock3 (3134801, 3, 1, 5, 2 ^ 4 * 5 ^ 2),
   pock3 (897064739519922787230182993783, 5, 1, 3, 2 * 73 * 487 * 3134801),
   pock3 (1361129467683753853853498429727072845819, 2, 1, 0, 2 * 23 * 32985101
     * 897064739519922787230182993783)]

/-- **Theorem 3.1** (Bernstein 2005): `2^130 - 5` is prime. -/
theorem P_prime : Nat.Prime P :=  prime_two_pow_130_sub_5

end Poly1305Prime
