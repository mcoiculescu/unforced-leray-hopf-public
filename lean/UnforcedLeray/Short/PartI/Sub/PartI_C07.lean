import UnforcedLeray.Short.PartI.Sub.PartI_C06
import UnforcedLeray.Short.PartI.Tasks.GreenEllipticRegularity
import UnforcedLeray.Short.Spine.Proofs.CanonicalBranch.Regularity.Smoothing
import UnforcedLeray.Short.Spine.Proofs.CanonicalBranch.Regularity.Strong
import UnforcedLeray.Short.Spine.Proofs.CanonicalBranch.Regularity.Bootstrap

/-!
# Part I, task `PartI:C07`: the mild canonical solution is strong and smooth

Source of record: `the November 2 reference manuscript`,
lines 1126-1146 (smoothness for positive `θ` by the local argument: heat gain
`‖e^{aD}‖_{X_{G,j}→X_{G,j+1}} ≤ C_j a^{-1/2}`, `L` bounded on `X_{G,j}`, Duhamel gains a derivative).

The regularity theory is already proved on the Spine for a curve that is mild on all of `(0,∞)`
for the concrete backward evolution `S` (`Spine.mildSpatialSmoothing`, `mildIsStrong`,
`strongBootstrap`, with `PartI.greenEllipticRegularity`).  What is missing is the passage from the
coupled mild system of `PartI:C06` on `[b,∞)` to mildness for `S`, extended below `b` by
`V(θ) = S(θ,b)V(b)` (`CanonicalMildIsMildOnPos`, the only open input).
-/

set_option autoImplicit false

noncomputable section

open Set
open scoped ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray

/-- `IDpow 0` is the identity (every multiplier is `(1+n)^0 = 1`). -/
theorem IDpow_zero_apply (f : B0010.XG) (h : f ∈ (B0123.IDpow 0).domain) :
    B0123.IDpow 0 ⟨f, h⟩ = f := by
  refine B0094.ext_inner_basis B0094.oscBasis fun n => ?_
  unfold B0123.IDpow
  rw [B0123.inner_mulOp]
  simp [B0123.idMult]

theorem IDpow_of_eq_zero {s : ℝ} (hs : s = 0) (f : B0010.XG) (h : f ∈ (B0123.IDpow s).domain) :
    B0123.IDpow s ⟨f, h⟩ = f := by
  subst hs
  exact IDpow_zero_apply f h

/-- A curve that is mild on `(0,∞)` for the concrete backward evolution `S` is a canonical
solution in the sense of `IsCanonicalSolution` (all inputs are the proved Spine theorems). -/
theorem isCanonicalSolution_of_mildOnPos {W : ℝ → B0010.XG} (hW : Spine.IsMildOnPos W) :
    IsCanonicalSolution W := by
  have hG : Spine.GreenAll := fun j => greenEllipticRegularity j
  have hstr := Spine.mildIsStrong hG W hW
  have hcont := Spine.mildSpatialSmoothing hG W hW
  have hsm := Spine.strongBootstrap hG W hcont hstr
  refine ⟨fun θ hθ => (hstr θ hθ).choose, ?_, fun θ hθ => ?_⟩
  · obtain ⟨U, hU, hUd⟩ := hsm 0
    refine hUd.congr fun θ hθ => ?_
    obtain ⟨h, e⟩ := hU θ hθ
    have h0 : ((0 : ℕ) : ℝ) / 2 = 0 := by simp
    rw [← e]
    exact (IDpow_of_eq_zero h0 _ _).symm
  · obtain ⟨h, hd⟩ := hstr θ hθ
    rw [hd.deriv, neg_neg]
    rfl

/-- **The only open input** (source lines 1094-1122, 1126-1146): a mild solution of the coupled
system of `IsCanonicalMild` on `[b,∞)` (`b > 0`) is the restriction of a curve `W` mild on `(0,∞)`
for the evolution `S(θ,θ')` of `-V' = (L + θ⁻¹D)V` (`W θ = S θ b (V b)` below `b`). -/
def CanonicalMildIsMildOnPos : Prop :=
  ∀ (lam : ℂ) (q : B0010.XG) (l : B0010.XG →L[ℂ] ℂ), IsSeedXG lam q l →
    ∀ (qd : B0010.XG), (∀ f, l f = inner ℂ qd f) →
    ∀ (hq : q ∈ B0094.D.domain) (hqd : qd ∈ B0094.D.domain) (b : ℝ), 0 < b →
    ∀ V : ℝ → B0010.XG, IsCanonicalMild lam q l qd hq hqd b V →
      ∃ W : ℝ → B0010.XG, Spine.IsMildOnPos W ∧ ∀ θ, b ≤ θ → W θ = V θ

theorem canonical_mild_is_strong_smooth_of (h : CanonicalMildIsMildOnPos)
    {lam : ℂ} {q : B0010.XG} {l : B0010.XG →L[ℂ] ℂ} (hI : IsSeedXG lam q l) {qd : B0010.XG}
    (hl : ∀ f, l f = inner ℂ qd f) (hq : q ∈ B0094.D.domain) (hqd : qd ∈ B0094.D.domain)
    {b : ℝ} (hb : 0 < b) {V : ℝ → B0010.XG} (hV : IsCanonicalMild lam q l qd hq hqd b V) :
    ∃ hmem : ∀ θ : ℝ, b < θ → V θ ∈ B0094.D.domain,
      ContDiffOn ℝ ∞ V (Ioi b) ∧
      ∀ (θ : ℝ) (hθ : b < θ),
        -(deriv V θ) = Planar.L0 (V θ) + ((θ : ℂ)⁻¹) • B0094.D ⟨V θ, hmem θ hθ⟩ := by
  obtain ⟨W, hW, hWV⟩ := h lam q l hI qd hl hq hqd b hb V hV
  have hC := isCanonicalSolution_of_mildOnPos hW
  have hev : ∀ θ, b < θ → W =ᶠ[nhds θ] V := fun θ hθ =>
    Filter.eventually_of_mem (Ioi_mem_nhds hθ) fun x hx => hWV x (le_of_lt hx)
  have hmem : ∀ θ : ℝ, b < θ → V θ ∈ B0094.D.domain := fun θ hθ => by
    rw [← hWV θ hθ.le]; exact hC.mem_domain θ (hb.trans hθ)
  refine ⟨hmem, ?_, fun θ hθ => ?_⟩
  · refine (hC.smooth.mono (Ioi_subset_Ioi hb.le)).congr fun θ hθ => ?_
    exact (hWV θ (le_of_lt hθ)).symm
  · have := hC.equation θ (hb.trans hθ)
    rw [(hev θ hθ).deriv_eq] at this
    have key : ∀ (x y : B0010.XG) (hx : x ∈ B0094.D.domain) (hy : y ∈ B0094.D.domain),
        x = y → B0094.D ⟨x, hx⟩ = B0094.D ⟨y, hy⟩ := by
      intro x y hx hy hxy; subst hxy; rfl
    rw [key (V θ) (W θ) (hmem θ hθ) (hC.mem_domain θ (hb.trans hθ)) (hWV θ hθ.le).symm, ← hWV θ hθ.le, ← this]

end UnforcedLeray.Short.PartI
