import UniversalHashing

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


section toeplitz


/- The binary matrix ``\begin{pmatrix}  1 & 0 \\ 1 & 1 \end{pmatrix}`` is Toeplitz. -/
example : !![(1 : ZMod 2), 0,
              1,           1].IsToeplitz := by
  intro i j
  fin_cases i; fin_cases j
  repeat simp_all
  decide

/-- The binary matrix ``\begin{pmatrix}  0 & 1 \\ 1 & 1 \end{pmatrix}`` is **NOT** Toeplitz
 because the main diagonal is not constant. -/
example : ¬ !![(0 : ZMod 2), 1;
                1,           1].IsToeplitz := by
  intro h
  have : !![(0 : ZMod 2), 1; 1, 1] 0 0 = 1 :=
      calc !![(0 : ZMod 2), 1; 1, 1] 0 0
      _ = !![(0 : ZMod 2), 1; 1, 1] 1 1 := by
          apply h
          simp only [Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod, Nat.mod_succ, zero_add]
      _ = 1 := by dsimp
  have : !![(0 : ZMod 2), 1; 1, 1] 0 0 = 0 := by dsimp
  contradiction

end toeplitz

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
    := binToeplitz_mulVec_isUniversal2 2 3

end Example_2x3
