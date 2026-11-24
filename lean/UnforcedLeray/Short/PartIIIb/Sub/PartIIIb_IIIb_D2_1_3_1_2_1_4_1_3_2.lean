import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_4_1_3
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_4_1_3_2_props

/-!
# `selCauchy`: assembly

Source `the November 2 reference manuscript` lines 1351-1362, 1470-1480.
`SelCauchyY` is `SelCauchy` with the two missing membership hypotheses `Φ, a ∈ Y_2` (without
`Φ` measurable, `YConv` is a statement about a lower integral and gives no Cauchy property).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- `SelCauchy` with `Φ, a ∈ Y_2` as hypotheses. -/
def SelCauchyY : Prop :=
  ∀ (P ν : ℝ), 0 < P → 0 < ν → ∀ (Φ a : ℝ × Space → CVec3)
    (Ψ A : ℕ → ℝ × Space → CVec3) (D : ℕ → Fin 3 → ℝ × Space → CVec3),
    UnforcedLeray.Short.IIb.IsInYr P 2 Φ → UnforcedLeray.Short.IIb.IsInYr P 2 a →
    (∀ n, UnforcedLeray.Short.IIb.IsInYr P 2 (Ψ n)) →
    (∀ n, UnforcedLeray.Short.IIb.IsInYr P 2 (A n)) →
    (∀ n j, UnforcedLeray.Short.IIb.IsInYr P 2 (D n j)) →
    YConv P Ψ Φ → YConv P A a →
    (∀ n, SliceLapId ν (Ψ n) (A n)) →
    (∀ n j, SliceWeakD (Ψ n) j (D n j)) →
      ∀ j, YCauchy P (fun n => D n j)

/-- (C6) Convergence implies Cauchy in `Y_2` (source 1341-1344): `Ψₙ, Φ ∈ Y_2`,
`‖Ψₙ - Φ‖ → 0` gives `‖Ψₙ - Ψₘ‖ → 0` (`phaseLpTri2` / `phaseLpNorm_add_le` in
`AdjTruncOrg.lean`, triangle inequality applied to `(Ψₙ - Φ) + (Φ - Ψₘ)`). -/
def CYConvCauchy : Prop :=
  ∀ (P : ℝ), 0 < P → ∀ (Ψ : ℕ → ℝ × Space → CVec3) (Φ : ℝ × Space → CVec3),
    (∀ n, UnforcedLeray.Short.IIb.IsInYr P 2 (Ψ n)) → UnforcedLeray.Short.IIb.IsInYr P 2 Φ →
      YConv P Ψ Φ → YCauchy P Ψ

/-- (C7) `Y_2` is closed under differences (source 1334-1337): periodic a.e., measurable,
finite norm by Minkowski (`phaseLpNorm_add_le`, `AdjTruncOrg.lean:249`). -/
def CYrSub : Prop :=
  ∀ (P : ℝ), 0 < P → ∀ f g : ℝ × Space → CVec3,
    UnforcedLeray.Short.IIb.IsInYr P 2 f → UnforcedLeray.Short.IIb.IsInYr P 2 g →
      UnforcedLeray.Short.IIb.IsInYr P 2 (fun x => f x - g x)

theorem selCauchyY_of (h1 : CSliceEnergy) (h2 : CSliceAe) (h3a : CLapDiff) (h3b : CWeakDiff)
    (h4 : CYEnergy) (h5 : CEnnrealCauchy) (h6 : CYConvCauchy) (h7 : CYrSub) : SelCauchyY := by
  intro P ν hP hν Φ a Ψ A D hΦ ha hΨ hA hD hΨΦ hAa hlap hwk j
  have cΨ := h6 P hP Ψ Φ hΨ hΦ hΨΦ
  have cA := h6 P hP A a hA ha hAa
  have key : ∀ n m, (UnforcedLeray.Short.IIb.phaseLpNorm P 2 (fun x => D n j x - D m j x)) ^ (2 : ℝ)
      ≤ ENNReal.ofReal ν⁻¹ * UnforcedLeray.Short.IIb.phaseLpNorm P 2 (fun x => Ψ n x - Ψ m x)
        * UnforcedLeray.Short.IIb.phaseLpNorm P 2 (fun x => A n x - A m x) := by
    intro n m
    have hE := h4 P ν hP hν (fun x => Ψ n x - Ψ m x) (fun x => A n x - A m x)
      (fun k x => D n k x - D m k x) (h7 P hP _ _ (hΨ n) (hΨ m)) (h7 P hP _ _ (hA n) (hA m))
      (fun k => h7 P hP _ _ (hD n k) (hD m k)) ?_
    · refine le_trans ?_ hE
      exact Finset.single_le_sum (f := fun k : Fin 3 =>
        UnforcedLeray.Short.IIb.phaseLpNorm P 2 (fun x => D n k x - D m k x) ^ (2 : ℝ))
        (fun _ _ => zero_le) (Finset.mem_univ j)
    · -- a.e. slice bound
      have s1 : ∀ᵐ τ : ℝ, ∀ n, MemLp (fun y : Space => Ψ n (τ, y)) 2 volume :=
        ae_all_iff.2 fun n => h2 P hP _ (hΨ n)
      have s2 : ∀ᵐ τ : ℝ, ∀ n, MemLp (fun y : Space => A n (τ, y)) 2 volume :=
        ae_all_iff.2 fun n => h2 P hP _ (hA n)
      have s3 : ∀ᵐ τ : ℝ, ∀ n k, MemLp (fun y : Space => D n k (τ, y)) 2 volume :=
        ae_all_iff.2 fun n => ae_all_iff.2 fun k => h2 P hP _ (hD n k)
      have s4 : ∀ᵐ τ : ℝ, ∀ n, ∀ θ : Space → CVec3, ContDiff ℝ ∞ θ → HasCompactSupport θ →
          ν * (∫ y : Space, ∑ i : Fin 3, Ψ n (τ, y) i * lapS θ y i)
            = ∫ y : Space, ∑ i : Fin 3, A n (τ, y) i * θ y i :=
        ae_all_iff.2 fun n => hlap n
      have s5 : ∀ᵐ τ : ℝ, ∀ n k, ∀ θ : Space → CVec3, ContDiff ℝ ∞ θ → HasCompactSupport θ →
          -(∫ y : Space, ∑ i : Fin 3, Ψ n (τ, y) i *
              fderiv ℝ (fun z => θ z i) y (EuclideanSpace.single k (1 : ℝ)))
            = ∫ y : Space, ∑ i : Fin 3, D n k (τ, y) i * θ y i :=
        ae_all_iff.2 fun n => ae_all_iff.2 fun k => hwk n k
      filter_upwards [s1, s2, s3, s4, s5] with τ t1 t2 t3 t4 t5
      have := h1 ν hν (fun y => Ψ n (τ, y) - Ψ m (τ, y)) (fun y => A n (τ, y) - A m (τ, y))
        (fun k y => D n k (τ, y) - D m k (τ, y)) ((t1 n).sub (t1 m)) ((t2 n).sub (t2 m))
        (fun k => (t3 n k).sub (t3 m k))
        (h3a ν _ _ _ _ (t1 n) (t1 m) (t2 n) (t2 m) (t4 n) (t4 m))
        (fun k => h3b k _ _ _ _ (t1 n) (t1 m) (t3 n k) (t3 m k) (t5 n k) (t5 m k))
      exact this
  exact h5 _ _ _ (ENNReal.ofReal ν⁻¹) ENNReal.ofReal_ne_top cΨ cA key

end UnforcedLeray.Short.PartIIIb.Concrete
