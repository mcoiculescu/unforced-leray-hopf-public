import UnforcedLeray.Short.PartIIIa.Sub.T18_3_1_3_2
import UnforcedLeray.Lib.BochnerTime.Energy

/-!
# `PartIII-a:T18/3/1/3/2/1` (`lmEnergyBridge`), decomposed

Source: `the November 2 reference manuscript` 3541-3552.  The `ℂ²`-valued fields are
identified with elements of the real Hilbert space `LMH c = L²(cell; ℝ⁴)` (real and imaginary parts
of the two components), so that `Lib/BochnerTime` applies.  Three leaf statements
(`LMRepExists`, `LMRepIdentity`, `LMRepPair`) give the identification; `lmEnergyBridge_of`
assembles `LMEnergyBridge` via `HasWeakDerivTime.weighted_norm_sq_sub`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open UnforcedLeray.BochnerTime
open scoped ENNReal ContDiff RealInnerProductSpace

namespace UnforcedLeray.Short.IIIa

/-- The real Hilbert space `L²(cell; ℝ⁴)`. -/
abbrev LMH (c : ℝ) : Type :=
  MeasureTheory.Lp (EuclideanSpace ℝ (Fin 4)) 2 (volume.restrict (B0579.cell c))

/-- Real and imaginary parts of both components, as a vector of `ℝ⁴`. -/
def lmReal (z : Fin 2 → ℂ) : EuclideanSpace ℝ (Fin 4) :=
  !₂[(z 0).re, (z 0).im, (z 1).re, (z 1).im]

/-- `U` represents the family `u`: for a.e. `s > 0`, `U s` is a.e. equal to `lmReal ∘ u s`. -/
def LMRep (c : ℝ) (u : ℝ → LMSpField) (U : ℝ → LMH c) : Prop :=
  ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))),
    ∀ᵐ x ∂(volume.restrict (B0579.cell c)), (U s : ℝ × ℝ → EuclideanSpace ℝ (Fin 4)) x =
      lmReal (u s x)

/-- **Leaf 1 (measurability bridge)**: joint measurability and local `L²` bounds give `LMH`-valued
representatives, Bochner integrable on every `Ioo a b`, `0 < a < b` (Cauchy-Schwarz in `x` and
`s`; Fubini for the `L²` norms). -/
def LMRepExists : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ u u' : ℝ → LMSpField, LMWeakDeriv c u u' →
    ∃ U U' : ℝ → LMH c, LMRep c u U ∧ LMRep c u' U' ∧ ∀ a b : ℝ, 0 < a → a < b →
      IntegrableOn U (Ioo a b) ∧ IntegrableOn U' (Ioo a b)

/-- **Leaf 2 (the tested identity)**: the identity of `LMWeakDeriv` (tested against every
`χ ∈ L²(cell)`, SP 3541-3552) gives the Bochner identity `∫ ψ' • U = -∫ ψ • U'` in `LMH c`
(`integral_inner`, and a Hilbert-space element is determined by its pairings with all `χ`, each
`χ ∈ LMH c` having a `LMSpField` representative with `LMCellL2`). -/
def LMRepIdentity : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ u u' : ℝ → LMSpField, LMWeakDeriv c u u' →
    ∀ U U' : ℝ → LMH c, LMRep c u U → LMRep c u' U' →
      (∀ a b : ℝ, 0 < a → a < b → IntegrableOn U (Ioo a b) ∧ IntegrableOn U' (Ioo a b)) →
      ∀ a b : ℝ, 0 < a → a < b → ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ Ioo a b → ∫ t, deriv ψ t • U t = -∫ t, ψ t • U' t

/-- **Leaf 3 (norm and pairing)**: for representatives, a.e. `s > 0`,
`‖U s‖² = ∫_cell |u s|²` and `⟪U' s, U s⟫ = Re ⟨u' s, u s⟩_{L²(cell;ℂ²)}`; and these two scalar
functions of `s` are integrable on every `Ioo a b`, `0 < a < b`. -/
def LMRepPair : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ u u' : ℝ → LMSpField, LMWeakDeriv c u u' →
    ∀ U U' : ℝ → LMH c, LMRep c u U → LMRep c u' U' →
      (∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))),
        ‖U s‖ ^ 2 = ∫ x in B0579.cell c, vnorm2 (u s x) ^ 2 ∧
          ⟪U' s, U s⟫ = (LMIp c (u' s) (u s)).re) ∧
      ∀ a b : ℝ, 0 < a → a < b →
        IntegrableOn (fun s => ∫ x in B0579.cell c, vnorm2 (u s x) ^ 2) (Ioo a b) ∧
          IntegrableOn (fun s => (LMIp c (u' s) (u s)).re) (Ioo a b)

theorem lmEnergyBridge_of (h1 : LMRepExists) (h2 : LMRepIdentity) (h3 : LMRepPair) :
    LMEnergyBridge := by
  intro c hc u u' hW w hw hcs hts
  obtain ⟨U, U', hU, hU', hint⟩ := h1 c hc u u' hW
  have hpair := h3 c hc u u' hW U U' hU hU'
  -- a compact interval `[a', b']` inside `(0, ∞)` containing the support of `w`
  obtain ⟨a, b, ha, hab, hsub⟩ : ∃ a b : ℝ, 0 < a ∧ a < b ∧ tsupport w ⊆ Ioo a b := by
    have hK := hcs
    rcases (tsupport w).eq_empty_or_nonempty with he | hne
    · exact ⟨1, 2, one_pos, one_lt_two, by simp [he]⟩
    · obtain ⟨x0, hx0, hmin⟩ := hK.exists_isMinOn hne continuous_id.continuousOn
      obtain ⟨y0, hy0, hmax⟩ := hK.exists_isMaxOn hne continuous_id.continuousOn
      have hx0pos : 0 < x0 := hts hx0
      refine ⟨x0 / 2, y0 + 1, by positivity, ?_, fun x hx => ⟨?_, ?_⟩⟩
      · have := hmax hx0; simp at this; linarith
      · have := hmin hx; simp at this; linarith
      · have := hmax hx; simp at this; linarith
  have hweak : HasWeakDerivTime a b U U' :=
    ⟨(hint a b ha hab).1, (hint a b ha hab).2,
      fun ψ hψ hψc hψt => h2 c hc u u' hW U U' hU hU' hint a b ha hab ψ hψ hψc hψt⟩
  have hwa : w a = 0 := image_eq_zero_of_notMem_tsupport (fun h => (hsub h).1.false)
  have hwb : w b = 0 := image_eq_zero_of_notMem_tsupport (fun h => (hsub h).2.false)
  have hE := hweak.weighted_norm_sq_sub (hw.of_le (by exact_mod_cast le_top)) (s := a) (t := b)
    ⟨le_rfl, hab.le⟩ ⟨hab.le, le_rfl⟩
  rw [hwa, hwb] at hE
  obtain ⟨hpa, hpi⟩ := hpair
  obtain ⟨hA, hB⟩ := hpi a b ha hab
  set A : ℝ → ℝ := fun s => ∫ x in B0579.cell c, vnorm2 (u s x) ^ 2 with hAdef
  set B : ℝ → ℝ := fun s => (LMIp c (u' s) (u s)).re with hBdef
  have hsupp : ∀ s, s ∉ Ioo a b → w s = 0 ∧ deriv w s = 0 := fun s hs =>
    ⟨image_eq_zero_of_notMem_tsupport (fun h => hs (hsub h)),
      by
        by_contra hne
        exact hs (hsub (support_deriv_subset (Function.mem_support.2 hne)))⟩
  have hwc : Continuous w := hw.continuous
  have hdc : Continuous (deriv w) := hw.continuous_deriv (by simp)
  have hbw : ∃ M, ∀ s, |w s| ≤ M := by
    obtain ⟨M, hM⟩ := hcs.exists_bound_of_continuous hwc
    exact ⟨M, fun s => by simpa using hM s⟩
  have hbd : ∃ M, ∀ s, |deriv w s| ≤ M := by
    obtain ⟨M, hM⟩ := hcs.deriv.exists_bound_of_continuous hdc
    exact ⟨M, fun s => by simpa using hM s⟩
  have hint1 : IntegrableOn (fun s => deriv w s * A s) (Ioo a b) := by
    obtain ⟨M, hM⟩ := hbd
    refine Integrable.bdd_mul (c := M) hA ?_ ?_
    · exact hdc.aestronglyMeasurable
    · exact Filter.Eventually.of_forall (fun s => by simpa using hM s)
  have hint2 : IntegrableOn (fun s => w s * B s) (Ioo a b) := by
    obtain ⟨M, hM⟩ := hbw
    refine Integrable.bdd_mul (c := M) hB ?_ ?_
    · exact hwc.aestronglyMeasurable
    · exact Filter.Eventually.of_forall (fun s => by simpa using hM s)
  have hIoi : ∀ f : ℝ → ℝ, (∀ s, s ∉ Ioo a b → f s = 0) →
      ∫ s in Ioi (0 : ℝ), f s = ∫ s in Ioo a b, f s := by
    intro f hf
    refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi ?_ ?_
    · intro x hx; exact lt_trans ha hx.1
    · intro x hx
      exact hf x hx.2
  have e1 : ∫ s in Ioi (0 : ℝ), deriv w s * A s = ∫ s in Ioo a b, deriv w s * A s :=
    hIoi _ (fun s hs => by simp [(hsupp s hs).2])
  have e2 : ∫ s in Ioi (0 : ℝ), w s * (2 * B s) = ∫ s in Ioo a b, w s * (2 * B s) :=
    hIoi _ (fun s hs => by simp [(hsupp s hs).1])
  have e3 : ∫ s in Ioo a b, w s * (2 * B s) = 2 * ∫ s in Ioo a b, w s * B s := by
    rw [← integral_const_mul]; congr 1; ext s; ring
  have hIcc : ∀ᵐ r ∂(volume.restrict (Ioo a b)),
      deriv w r * ‖hweak.rep r‖ ^ 2 + 2 * w r * ⟪U' r, hweak.rep r⟫ =
        deriv w r * A r + 2 * (w r * B r) := by
    have h0 := hweak.ae_eq_rep
    have hp : ∀ᵐ s ∂(volume.restrict (Ioo a b)), s ∈ Ioi (0:ℝ) ∧
        (‖U s‖ ^ 2 = A s ∧ ⟪U' s, U s⟫ = B s) := by
      rw [ae_restrict_iff' measurableSet_Ioo]
      have := (ae_restrict_iff' measurableSet_Ioi).1 hpa
      filter_upwards [this] with s hs hsI
      exact ⟨lt_trans ha hsI.1, hs (lt_trans ha hsI.1)⟩
    filter_upwards [h0, hp] with r hr hr2
    rw [← hr, hr2.2.1, hr2.2.2]; ring
  have hmain : ∫ r in a..b, (deriv w r * ‖hweak.rep r‖ ^ 2 + 2 * w r * ⟪U' r, hweak.rep r⟫) =
      (∫ s in Ioo a b, deriv w s * A s) + 2 * ∫ s in Ioo a b, w s * B s := by
    rw [intervalIntegral.integral_of_le hab.le, integral_Ioc_eq_integral_Ioo,
      integral_congr_ae hIcc, integral_add hint1 (hint2.const_mul 2),
      integral_const_mul]
  rw [hmain] at hE
  show ∫ s in Ioi (0 : ℝ), deriv w s * A s = -∫ s in Ioi (0 : ℝ), w s * (2 * B s)
  rw [e1, e2, e3]
  linarith

end UnforcedLeray.Short.IIIa
