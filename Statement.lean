/-!
# Statement v1 (Lucas): stored geodesic matrix has an exact 2:1 growth ratio (toy two-torus model, one geodesic)

Written against Link's frozen checklist `/workspace/link/a_to_ratio_target_v1/TARGET_CHECKLIST_v1.md`
(sha be2fc43d…). Frozen (hashed) before Proof.lean was written. Core Lean 4.35.0, no Mathlib.

T1 SOURCE. `data/kz_along_A.json` in HeywoodGeblomi/omega-ed6-h1plus-measure @ b7c4a7a56595eb26f26324318613f3c61fe53a28,
   sha256 06e6a20f0bdd14dc6c31fc1a174aa09c1286abd1fa0f2bee2dd6ed19e740a50e. `M` and `A` below are pasted from
   `gen_matrix.py` output (`gen_output.txt`, sha256 762921656f03ef2cd968146cbc234a02a2eb38bb1c499994a244e63cf3b93eee).
   `M` is the file's `M_plus` (basis c0, c1, c2, c3 as stored); `A` is the file's `A`.
T7 MODEL. These matrices are reproduced by Lucas's simplified two-torus model (two separate tori, transvection letters).
   No real Prym H(6) surface producing them was found (105 square-tiled candidates tried). Names say `ToyTwoTorus`.
T6 SCOPE. Everything here is about this one closed geodesic (path-local). Nothing claims Lyapunov exponents of the
   locus or a Masur–Veech average.
T5 TIE TO A. There is NO sub-action: M has no eigenvalue equal to ρ(A) = 26+15√3 or its inverse, so M does not act by A
   on any invariant plane. The only tie proved is numerical: with s = 2+√3, ρ(A) = s³ and M's top two growth rates are
   s² and s, so per unit of log ρ(A) the rates are 2/3 and 1/3 of this geodesic. (For Prym eigenforms the form itself
   lies in the minus part, so A acting off the plus part is expected; this file does not prove that.)
T10 Not attempted: no theorem here carries the ratio into 4/7, 2/7.

ENCODING (reader must accept): a + b√3 is the integer pair `⟨a, b⟩`; `Z3.Pos` is the exact integer sign test for
a + b√3 > 0. Polynomials are integer coefficient lists, lowest degree first. Matrices are lists of integer rows.
-/
namespace ToyGeodesic

structure Z3 where
  a : Int
  b : Int
deriving DecidableEq, Repr

namespace Z3
def add (x y : Z3) : Z3 := ⟨x.a + y.a, x.b + y.b⟩
def mul (x y : Z3) : Z3 := ⟨x.a * y.a + 3 * x.b * y.b, x.a * y.b + x.b * y.a⟩
def neg (x : Z3) : Z3 := ⟨-x.a, -x.b⟩
def ofInt (n : Int) : Z3 := ⟨n, 0⟩
def zero : Z3 := ⟨0, 0⟩
def one : Z3 := ⟨1, 0⟩
/-- Exact sign test: a + b√3 > 0. -/
def posB (x : Z3) : Bool :=
  if decide (x.a ≥ 0) && decide (x.b ≥ 0) then decide (x.a > 0) || decide (x.b > 0)
  else if decide (x.a > 0) && decide (x.b < 0) then decide (x.a * x.a > 3 * x.b * x.b)
  else if decide (x.a < 0) && decide (x.b > 0) then decide (3 * x.b * x.b > x.a * x.a)
  else false
def Pos (x : Z3) : Prop := posB x = true
/-- x > y as real numbers. -/
def Gt (x y : Z3) : Prop := Pos (add x (neg y))
end Z3

abbrev IMat := List (List Int)
abbrev IPoly := List Int

-- T1/T2: the stored matrices, defined once, pasted from gen_output.txt.
def M : IMat := [[-15, 0, -2, 0], [0, 1, 0, -3], [8, 0, 1, 0], [0, 2, 0, -5]]
def A : IMat := [[31, 10], [65, 21]]

def dotZ : List Int → List Z3 → Z3
  | x :: xs, v :: vs => Z3.add (Z3.mul (Z3.ofInt x) v) (dotZ xs vs)
  | _, _ => Z3.zero
def mulVecZ (m : IMat) (v : List Z3) : List Z3 := m.map (fun row => dotZ row v)
def smulZ (l : Z3) (v : List Z3) : List Z3 := v.map (Z3.mul l)

-- polynomial arithmetic
def padd : IPoly → IPoly → IPoly
  | x :: xs, y :: ys => (x + y) :: padd xs ys
  | [], ys => ys
  | xs, [] => xs
def pscale (c : Int) (p : IPoly) : IPoly := p.map (c * ·)
def pmul : IPoly → IPoly → IPoly
  | [], _ => []
  | x :: xs, q => padd (pscale x q) (0 :: pmul xs q)
def pnorm (p : IPoly) : IPoly := ((p.reverse).dropWhile (· == 0)).reverse
def evalZ : IPoly → Z3 → Z3
  | [], _ => Z3.zero
  | c :: cs, x => Z3.add (Z3.ofInt c) (Z3.mul x (evalZ cs x))

-- characteristic polynomial det(tI − m) by first-row Laplace expansion
def withIdxFrom {α : Type} : Nat → List α → List (α × Nat)
  | _, [] => []
  | k, x :: xs => (x, k) :: withIdxFrom (k + 1) xs
def removeAt {α : Type} : List α → Nat → List α
  | [], _ => []
  | _ :: xs, 0 => xs
  | x :: xs, k + 1 => x :: removeAt xs k
def charMat (m : IMat) : List (List IPoly) :=
  (withIdxFrom 0 m).map fun (row, i) =>
    (withIdxFrom 0 row).map fun (x, j) => if i = j then [-x, 1] else [-x]
def det : Nat → List (List IPoly) → IPoly
  | 0, _ => [1]
  | n + 1, m =>
    match m with
    | [] => [1]
    | row :: rest =>
      (withIdxFrom 0 row).foldl
        (fun acc (x, j) =>
          padd acc (pmul (if j % 2 = 0 then x else pscale (-1) x) (det n (rest.map (fun r => removeAt r j)))))
        []
def charpoly (m : IMat) : IPoly := pnorm (det m.length (charMat m))

-- exact growth rates (moduli of eigenvalues), as elements of Z[√3]
def s : Z3 := ⟨2, 1⟩        -- second growth rate, 2 + √3
def r : Z3 := ⟨7, 4⟩        -- top growth rate, 7 + 4√3
def sInv : Z3 := ⟨2, -1⟩    -- 2 − √3
def rInv : Z3 := ⟨7, -4⟩    -- 7 − 4√3
def rhoA : Z3 := ⟨26, 15⟩   -- 26 + 15√3
def rhoAInv : Z3 := ⟨26, -15⟩

-- explicit eigenvectors of M (coordinates c0, c1, c2, c3)
def vR : List Z3 := [⟨1, 0⟩, ⟨0, 0⟩, ⟨-4, 2⟩, ⟨0, 0⟩]
def vRinv : List Z3 := [⟨1, 0⟩, ⟨0, 0⟩, ⟨-4, -2⟩, ⟨0, 0⟩]
def vS : List Z3 := [⟨0, 0⟩, ⟨3, 0⟩, ⟨0, 0⟩, ⟨3, 1⟩]
def vSinv : List Z3 := [⟨0, 0⟩, ⟨3, 0⟩, ⟨0, 0⟩, ⟨3, -1⟩]
def vA : List Z3 := [⟨10, 0⟩, ⟨-5, 15⟩]

/-- T4. Exact 2:1 along this one geodesic of the toy model. -/
def ToyTwoTorus_ThisGeodesic_GrowthTwoToOne : Prop :=
  -- the 2:1: top rate is exactly the square of the second, both > 1
  r = Z3.mul s s ∧ Z3.Gt s Z3.one ∧ Z3.Gt r Z3.one ∧
  -- four eigenpairs of M: −r, −r⁻¹, −s, −s⁻¹, with nonzero eigenvectors
  mulVecZ M vR = smulZ (Z3.neg r) vR ∧ mulVecZ M vRinv = smulZ (Z3.neg rInv) vRinv ∧
  mulVecZ M vS = smulZ (Z3.neg s) vS ∧ mulVecZ M vSinv = smulZ (Z3.neg sInv) vSinv ∧
  vR ≠ [Z3.zero, Z3.zero, Z3.zero, Z3.zero] ∧ vRinv ≠ [Z3.zero, Z3.zero, Z3.zero, Z3.zero] ∧
  vS ≠ [Z3.zero, Z3.zero, Z3.zero, Z3.zero] ∧ vSinv ≠ [Z3.zero, Z3.zero, Z3.zero, Z3.zero] ∧
  -- the characteristic polynomial of M factors as (t² + 14t + 1)(t² + 4t + 1) ...
  charpoly M = pmul [1, 14, 1] [1, 4, 1] ∧
  -- ... and those factors are (t + r)(t + r⁻¹) and (t + s)(t + s⁻¹), so these four are ALL the eigenvalues
  Z3.add r rInv = Z3.ofInt 14 ∧ Z3.mul r rInv = Z3.one ∧
  Z3.add s sInv = Z3.ofInt 4 ∧ Z3.mul s sInv = Z3.one ∧
  -- the other two moduli are positive and below s, so no other eigenvalue has modulus ≥ s
  Z3.Pos rInv ∧ Z3.Gt s rInv ∧ Z3.Pos sInv ∧ Z3.Gt s sInv

/-- T5. How A relates to M on this geodesic of the toy model: numerically only, not as a sub-action. -/
def ToyTwoTorus_ThisGeodesic_ATie : Prop :=
  mulVecZ A vA = smulZ rhoA vA ∧ charpoly A = [1, -52, 1] ∧
  Z3.add rhoA rhoAInv = Z3.ofInt 52 ∧ Z3.mul rhoA rhoAInv = Z3.one ∧
  rhoA = Z3.mul s r ∧
  -- M has no eigenvalue ρ(A) or ρ(A)⁻¹ (nor their negatives), so it acts by A on no invariant plane
  evalZ (charpoly M) rhoA ≠ Z3.zero ∧ evalZ (charpoly M) rhoAInv ≠ Z3.zero ∧
  evalZ (charpoly M) (Z3.neg rhoA) ≠ Z3.zero ∧ evalZ (charpoly M) (Z3.neg rhoAInv) ≠ Z3.zero

end ToyGeodesic
