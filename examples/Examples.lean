import UniversalHashing.Toeplitz
import UniversalHashing.Basic

/-!
Examples illustrating definitions elsewhere,
to ease understanding and make definitions more concrete
-/

-- Shows evaluated matrix multiplication
section MatMulExample

def M : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![0, 1, 1; 0, 0, 0; 1, 1, 1]

def v : Fin 3 → ZMod 2 := ![1, 0, 1]

#eval M.mulVec v

end MatMulExample

section Example_2x3

/-- The most general binary 2x3 Toeplitz matrix -/
def Toeplitz2x3 (t1 t2 t3 t4 : ZMod 2) : Matrix (Fin 2) (Fin 3) (ZMod 2) :=
    !![
        t1, t3, t4;
        t2, t1, t3
    ]

example (t1 t2 t3 t4 : ZMod 2) : (Toeplitz2x3 t1 t2 t3 t4).IsToeplitz := by
  simp only [Toeplitz2x3, Matrix.IsToeplitz]
  fin_cases t1 <;>  fin_cases t2 <;>  fin_cases t3 <;>  fin_cases t4 <;>
  decide

/-- 3x2 Toeplitz matrices give a universal hash family (apply general result). -/
example :
    HashFamily.universal2 (fun (M : BinToeplitzMatrix 2 3) (v : Fin 3 → ZMod 2) => M.val.mulVec v)
    := by
  have : 2 ≤ 3 := Nat.AtLeastTwo.prop
  exact toeplitz_mulVec_isUniversal2 this

end Example_2x3
