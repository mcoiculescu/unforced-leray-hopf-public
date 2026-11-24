import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.HkStep.Shared
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_1.KernelDefs

/-!
# The adjoint localized interaction of order `-1` at every level: the leaves

Source of record: `the November 2 reference manuscript` (SP), lines 3052-3058:
"the adjoint localized interaction maps `X_{-m,d}` to `H^1_{-m,d}` uniformly: its localized source
has uniformly bounded `L^1` and `L^2` norms by weighted Cauchy-Schwarz; split the Biot-Savart
kernel into its integrable near part and bounded far part, and use the uniform order-zero
multiplier bound for its derivative, including the horizontal mean".

Design (target `KTOrderMinusOne m`, `HkStep/Shared.lean`).  Write `KTAt m c j` for the statement at
a fixed level `j` and cell length `c` (`KTOrderMinusOne m` is `1 < m → ∀ c ≥ 1, ∀ j, KTAt m c j`).

* **Level `0`** (`KTBase`, assembled in `KT/Of.lean` as `ktBase_of` from `KTSource`, `KTPairInt`,
  `KTWeakMeas`, `KTWeakCong` and the proved `kernelAdjointBound`): SP 3052-3056, the source
  `F_l = f B_l` is in `L¹ ∩ L²` with norms `≤ C ‖f‖_{X_{-m,c}}` (`KTSource`), `K_c^T F` has weak
  gradient in `X_{-m,c}` with `H¹` norm `≤ C (‖F‖₁ + ‖F‖₂)` (`KernelAdjointBound`), taken in its
  periodic representative.
* **Induction** (`KT/Of.lean`, `kTOrderMinusOne_of`): `χ = K_c^T(f B)` has
  `∂_kχ = K_c^T((∂_k f) B) + K_c^T(f ∂_kB)` (`KTCommute`, the commutation of the translation
  invariant kernel with `∂_k`); both summands are at level `j - 1` for the data `(∂_k f, B)` and
  `(f, ∂_kB)` (`KTCoeffDeriv` gives the bounds of the coefficient `∂_kB`), so `χ ∈ H^{j+1}` follows
  from the induction hypothesis (jets add: `KTJetAdd`).
* **Commutation** (`KTCommute`, assembled in `KT/CommuteOf.lean` from `KTWeakLeibniz`,
  `KTWeakIBP`, `KerVelSmooth`, `KTTestInt`, `KerVelIsBS'`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- The pairing characterisation of `χ = K_c^T(f B)` (the tail of `KTOrderMinusOne`): for every
cylinder test `ψ` of any circulation with kernel velocity `uψ`, `f (uψ·B)` is integrable on the cell
and `∫_{C_c} χ ψ = ∫_{C_c} f (uψ·B)`. -/
def KTPairing (c : ℝ) (f : ℝ × ℝ → ℂ) (B : Fin 2 → ℝ × ℝ → ℝ) (χ : ℝ × ℝ → ℂ) : Prop :=
  ∀ (ψ : ℝ × ℝ → ℝ) (uψ : ℝ × ℝ → Fin 2 → ℝ), B0579.IsCylTest c ψ →
    IsKernelBiotSavart c ψ uψ →
    IntegrableOn (fun x => f x * ((uψ x 0 * B 0 x + uψ x 1 * B 1 x : ℝ) : ℂ))
        (B0579.cell c) ∧
      ∫ x in B0579.cell c, χ x * (ψ x : ℂ) =
        ∫ x in B0579.cell c, f x * ((uψ x 0 * B 0 x + uψ x 1 * B 1 x : ℝ) : ℂ)

/-- The decay hypothesis on the coefficient field: `(1 + x₂²)^{(m+1)/2} ‖D^i B_l(x)‖ ≤ A`,
`i ≤ j`. -/
def KTCoeffBound (m : ℝ) (j : ℕ) (B : Fin 2 → ℝ × ℝ → ℝ) (A : ℝ) : Prop :=
  ∀ l (i : ℕ), i ≤ j → ∀ x : ℝ × ℝ,
    (1 + x.2 ^ 2) ^ ((m + 1) / 2) * ‖iteratedFDeriv ℝ i (B l) x‖ ≤ A

/-- The statement of `KTOrderMinusOne m` at a fixed cell length `c` and level `j` (after `1 < m`,
`1 ≤ c`). -/
def KTAt (m c : ℝ) (j : ℕ) : Prop :=
  ∀ (B : Fin 2 → ℝ × ℝ → ℝ) (A : ℝ),
    (∀ l, ContDiff ℝ ∞ (B l)) → (∀ l (x : ℝ × ℝ), B l (x.1 + c, x.2) = B l x) →
    KTCoeffBound m j B A →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : ℝ × ℝ → ℂ) (D : List (Fin 2) → ℝ × ℝ → ℂ), IsCellJet c m j f D →
      ∃ (χ : ℝ × ℝ → ℂ) (Dχ : List (Fin 2) → ℝ × ℝ → ℂ), IsCellJet c m (j + 1) χ Dχ ∧
        (∀ w : List (Fin 2), w.length ≤ j + 1 →
          xNorm c (-m) (Dχ w) ≤ ENNReal.ofReal C * jetNorm c m j D) ∧
        KTPairing c f B χ

/-- `KTOrderMinusOne m` is the family of the levels `KTAt m c j`. -/
theorem ktOrderMinusOne_iff (m : ℝ) :
    KTOrderMinusOne m ↔ (1 < m → ∀ c : ℝ, 1 ≤ c → ∀ j : ℕ, KTAt m c j) := Iff.rfl

/-! ## Level `0` -/

/-- **The level `0` statement** (SP 3052-3056). -/
def KTBase (m : ℝ) : Prop := 1 < m → ∀ c : ℝ, 1 ≤ c → KTAt m c 0

/-- **(KT-a) The localized source** (SP 3052-3053, weighted Cauchy-Schwarz): for `m > 1`, a continuous
coefficient field `B` with `(1 + x₂²)^{(m+1)/2} |B_l(x)| ≤ A` and `f ∈ X_{-m,c}` (`MemLp` for
`cellMeasure c (-m)`), each `f B_l` is integrable and in `L²` of the cell with
`‖f B_l‖_{L¹(C_c)} + ‖f B_l‖_{L²(C_c)} ≤ C ‖f‖_{X_{-m,c}}`, with `C = C(A, c, m)` chosen before `B`.  Proof: on the
cell `jb^{m} (1+x₂²)^{-(m+1)}`, with `jb = 1 + x₂²` the weight of `cellMeasure c (-m)`, is bounded
and `jb^{-1}` is bounded and integrable (`m > 1`); `|f B_l| ≤ A |f| jb^{-(m+1)/2}`; L²: bounded
`jb^{-(m+1)/2 + m/2} = jb^{-1/2}`; L¹: Cauchy-Schwarz with `∫_cell jb^{-1} < ∞`. -/
def KTSource : Prop :=
  ∀ (m : ℝ), 1 < m → ∀ c : ℝ, 0 < c → ∀ (A : ℝ),
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (B : Fin 2 → ℝ × ℝ → ℝ), (∀ l, Continuous (B l)) →
    (∀ l (x : ℝ × ℝ), (1 + x.2 ^ 2) ^ ((m + 1) / 2) * ‖B l x‖ ≤ A) →
    ∀ f : ℝ × ℝ → ℂ, MemLp f 2 (B0579.cellMeasure c (-m)) → ∀ l : Fin 2,
      IntegrableOn (fun x => f x * (B l x : ℂ)) (B0579.cell c) ∧
      MemLp (fun x => f x * (B l x : ℂ)) 2 (volume.restrict (B0579.cell c)) ∧
      eLpNorm (fun x => f x * (B l x : ℂ)) 1 (volume.restrict (B0579.cell c)) +
        eLpNorm (fun x => f x * (B l x : ℂ)) 2 (volume.restrict (B0579.cell c)) ≤
          ENNReal.ofReal C * xNorm c (-m) f

/-- **(KT-b) Integrability of the pairing** (SP 3056-3057, "including the horizontal mean"): for `F`
with every `F_l ∈ L¹ ∩ L²(C_c)`, a test `ψ` and a kernel velocity `uψ`, `Σ_l F_l uψ_l` is integrable
on the cell (`uψ_l = meanShear + L²`, the mean shear bounded, so `L¹ · L^∞ + L² · L²`). -/
def KTPairInt : Prop :=
  ∀ (c : ℝ) (F : Fin 2 → ℝ × ℝ → ℂ),
    (∀ l, IntegrableOn (F l) (B0579.cell c) ∧ MemLp (F l) 2 (volume.restrict (B0579.cell c))) →
    ∀ (ψ : ℝ × ℝ → ℝ) (uψ : ℝ × ℝ → Fin 2 → ℝ), B0579.IsCylTest c ψ → IsKernelBiotSavart c ψ uψ →
      IntegrableOn (fun x => F 0 x * ((uψ x 0 : ℝ) : ℂ) + F 1 x * ((uψ x 1 : ℝ) : ℂ))
        (B0579.cell c)

/-- **(KT-c) Weak derivatives have measurable representatives**: if `φ` has weak derivatives
`g_j` for both `j` (`HasWeakCellDerivC`, the pairings being integrable), then `φ` and every `g_j` are
a.e.-strongly measurable on the cell.  Proof: for `g_j` use the tests `ρ_n(x₂)` (smooth, periodic
trivially, `≥ 1` for `|x₂| ≤ n`): `g_j ρ_n` is integrable on the cell, hence a.e.-strongly
measurable, and `g_j = (g_j ρ_n)/ρ_n` on the band; countable union over `n`.  For `φ` use the tests
`ρ_n(x₂) sin(2πx₁/c)`, `ρ_n(x₂) cos(2πx₁/c)`: the sum `|∂_0 ψ_a| + |∂_0 ψ_b|` does not vanish on
`|x₂| < n` (and `φ ∂_0 ψ_a`, `φ ∂_0 ψ_b` are integrable); on the open set where `∂_0ψ_a ≠ 0` divide,
else use `ψ_b`. -/
def KTWeakMeas : Prop :=
  ∀ (c : ℝ) (φ : ℝ × ℝ → ℂ) (g : Fin 2 → ℝ × ℝ → ℂ), 0 < c →
    (∀ j, HasWeakCellDerivC c j φ (g j)) →
      AEStronglyMeasurable φ (volume.restrict (B0579.cell c)) ∧
      ∀ j, AEStronglyMeasurable (g j) (volume.restrict (B0579.cell c))

/-- **(KT-d) Weak derivatives only depend on the a.e. class on the cell**. -/
def KTWeakCong : Prop :=
  ∀ (c : ℝ) (j : Fin 2) (φ g φ' g' : ℝ × ℝ → ℂ),
    HasWeakCellDerivC c j φ g → φ' =ᵐ[volume.restrict (B0579.cell c)] φ →
      g' =ᵐ[volume.restrict (B0579.cell c)] g → HasWeakCellDerivC c j φ' g'

/-- **(KT-e) Weak derivatives add**. -/
def KTWeakAdd : Prop :=
  ∀ (c : ℝ) (j : Fin 2) (φ g φ' g' : ℝ × ℝ → ℂ),
    HasWeakCellDerivC c j φ g → HasWeakCellDerivC c j φ' g' →
      HasWeakCellDerivC c j (φ + φ') (g + g')

/-- **(KT-f) The derivative of a coefficient is a coefficient** (`iteratedFDeriv` of the
`fderiv`, `norm_iteratedFDeriv_fderiv`; `‖dir k‖ = 1`): if `B` is smooth, `c`-periodic, with the
decay bound up to order `j + 1`, then `∂_k B_l` (`B0579.pd k (B l)`) is smooth, `c`-periodic, with
the same constant up to order `j`. -/
def KTCoeffDeriv : Prop :=
  ∀ (m c : ℝ) (j : ℕ) (B : Fin 2 → ℝ × ℝ → ℝ) (A : ℝ) (k : Fin 2),
    (∀ l, ContDiff ℝ ∞ (B l)) → (∀ l (x : ℝ × ℝ), B l (x.1 + c, x.2) = B l x) →
    KTCoeffBound m (j + 1) B A →
    (∀ l, ContDiff ℝ ∞ (B0579.pd k (B l))) ∧
    (∀ l (x : ℝ × ℝ), B0579.pd k (B l) (x.1 + c, x.2) = B0579.pd k (B l) x) ∧
    KTCoeffBound m j (fun l => B0579.pd k (B l)) A

/-! ## Leaves of the commutation -/

/-- **(KT-h) Tests against `X_{-m,c}`**: for `φ ∈ X_{-m,c}` and a cylinder test `ψ` (compact support
in `x₂`, bounded), `φ ψ` is integrable on the cell (Cauchy-Schwarz with `jb^{m}` bounded on the
support of `ψ`; `B0579.IsCylTest.memLp`). -/
def KTTestInt : Prop :=
  ∀ (c m : ℝ), 0 < c → ∀ φ : ℝ × ℝ → ℂ, MemLp φ 2 (B0579.cellMeasure c (-m)) →
    ∀ ψ : ℝ × ℝ → ℝ, B0579.IsCylTest c ψ → IntegrableOn (fun x => φ x * (ψ x : ℂ)) (B0579.cell c)

/-- **(KT-i) The kernel velocity of a test is smooth, bounded, periodic, and `∂_k` commutes with
`K_c`** (SP 3056-3057: translation invariance of the kernel): for `d ≥ 1` and a test `ψ`,
`kerVel d ψ x j = ∫_{C_d} ψ(y) K_d(x - y)_j dy` is smooth in `x` (the derivative falls on the test:
write it as `∫ ψ(x - z) K_d(z) dz` over the period strip, `K_d` locally integrable, `d`-periodic),
`d`-periodic in `x₁`, bounded (`KerVelBdd`), and `∂_k (kerVel d ψ)_j = kerVel d (∂_kψ)_j`. -/
def KerVelSmooth : Prop :=
  ∀ d : ℝ, 1 ≤ d → ∀ ψ : ℝ × ℝ → ℝ, B0579.IsCylTest d ψ → ∀ j : Fin 2,
    ContDiff ℝ ∞ (fun x => kerVel d ψ x j) ∧
    (∀ (k : Fin 2) (x : ℝ × ℝ), B0579.pd k (fun y => kerVel d ψ y j) x = kerVel d (B0579.pd k ψ) x j) ∧
    (∃ M : ℝ, ∀ x : ℝ × ℝ, |kerVel d ψ x j| ≤ M) ∧
    (∀ x : ℝ × ℝ, kerVel d ψ (x.1 + d, x.2) j = kerVel d ψ x j)

/-- **(KT-j) The weak Leibniz rule** against a smooth, periodic, bounded factor with bounded
derivative: if `f, g ∈ X_{-m,c}` and `∂_k f = g` weakly, then `∂_k (f b) = g b + f ∂_k b` weakly.
Proof: `b ψ` is a test for a test `ψ` (`IsCylTest.mul`-type: smooth, periodic, vanishing for large
`|x₂|`), `∂_k(bψ) = b ∂_kψ + ψ ∂_k b`, so
`∫ f b ∂_kψ = ∫ f ∂_k(bψ) - ∫ f ψ ∂_k b = -∫ g b ψ - ∫ f ∂_k b ψ`; integrability by `KTTestInt`. -/
def KTWeakLeibniz : Prop :=
  ∀ (m c : ℝ), 0 < c → ∀ (k : Fin 2) (f g : ℝ × ℝ → ℂ) (b : ℝ × ℝ → ℝ),
    ContDiff ℝ ∞ b → (∀ x : ℝ × ℝ, b (x.1 + c, x.2) = b x) →
    (∃ M : ℝ, ∀ x : ℝ × ℝ, |b x| ≤ M ∧ |B0579.pd k b x| ≤ M) →
    HasWeakCellDerivC c k f g → MemLp f 2 (B0579.cellMeasure c (-m)) →
    MemLp g 2 (B0579.cellMeasure c (-m)) →
      HasWeakCellDerivC c k (fun x => f x * (b x : ℂ))
        (fun x => g x * (b x : ℂ) + f x * (B0579.pd k b x : ℂ))

/-- **(KT-k) Integration by parts against a smooth bounded field** (cutoff in `x₂`): if
`∂_k F = g'` weakly with `F, g' ∈ L¹(C_c)` and `G` is smooth, `c`-periodic, bounded with bounded
`∂_kG`, then `F ∂_kG` and `g' G` are integrable on the cell and `∫ F ∂_kG = -∫ g' G`.  Proof:
with `χ_R(x₂)` a smooth cutoff (`1` on `|x₂| ≤ R`, `0` for `|x₂| ≥ 2R`, `|χ_R'| ≤ 2/R`), `χ_R G` is
a test, `∫ F ∂_k(χ_R G) = -∫ g' χ_R G`; let `R → ∞` by dominated convergence (`F, g' ∈ L¹`, `G`,
`∂_kG` bounded, `∂_k χ_R = 0` for `k = 0`, `|F ∂_kχ_R G| ≤ (2/R) M |F|` for `k = 1`). -/
def KTWeakIBP : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ (k : Fin 2) (F g' : ℝ × ℝ → ℂ) (G : ℝ × ℝ → ℝ),
    HasWeakCellDerivC c k F g' → IntegrableOn F (B0579.cell c) → IntegrableOn g' (B0579.cell c) →
    ContDiff ℝ ∞ G → (∀ x : ℝ × ℝ, G (x.1 + c, x.2) = G x) →
    (∃ M : ℝ, ∀ x : ℝ × ℝ, |G x| ≤ M ∧ |B0579.pd k G x| ≤ M) →
      IntegrableOn (fun x => F x * (B0579.pd k G x : ℂ)) (B0579.cell c) ∧
      IntegrableOn (fun x => g' x * (G x : ℂ)) (B0579.cell c) ∧
      ∫ x in B0579.cell c, F x * (B0579.pd k G x : ℂ) = -∫ x in B0579.cell c, g' x * (G x : ℂ)

/-! ## The commutation with the derivative -/

/-- **(KT-g) The commutation** (SP 3052-3058, "the derivative is an order-zero multiplier"): with
`χ = K_c^T(f B)`, `χ₁ = K_c^T(g B)`, `χ₂ = K_c^T(f ∂_kB)` characterised by `KTPairing` and
`g = ∂_k f` weakly, one has `∂_kχ = χ₁ + χ₂` weakly.  Proof: for a test `ψ`, `∂_kψ` is a test, its
kernel velocity is `∂_k(K_cψ)` (`KerVelSmooth`), so
`∫ χ ∂_kψ = ∫ f (∂_k K_cψ · B) = -∫ g (K_cψ·B) - ∫ f (K_cψ·∂_kB) = -∫(χ₁+χ₂)ψ`
(`KTWeakLeibniz` for `f B_l`, then `KTWeakIBP` against the smooth bounded `(K_cψ)_l`). -/
def KTCommute (m : ℝ) : Prop :=
  1 < m → ∀ c : ℝ, 1 ≤ c → ∀ (B : Fin 2 → ℝ × ℝ → ℝ) (A : ℝ) (k : Fin 2),
    (∀ l, ContDiff ℝ ∞ (B l)) → (∀ l (x : ℝ × ℝ), B l (x.1 + c, x.2) = B l x) →
    KTCoeffBound m 1 B A →
    ∀ (f g χ χ₁ χ₂ : ℝ × ℝ → ℂ),
      MemLp f 2 (B0579.cellMeasure c (-m)) → MemLp g 2 (B0579.cellMeasure c (-m)) →
      MemLp χ 2 (B0579.cellMeasure c (-m)) → MemLp χ₁ 2 (B0579.cellMeasure c (-m)) →
      MemLp χ₂ 2 (B0579.cellMeasure c (-m)) → HasWeakCellDerivC c k f g →
      KTPairing c f B χ → KTPairing c g B χ₁ → KTPairing c f (fun l => B0579.pd k (B l)) χ₂ →
        HasWeakCellDerivC c k χ (χ₁ + χ₂)
