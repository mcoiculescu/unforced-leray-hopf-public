import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_delta_9
import UnforcedLeray.Short.PartIIIa.FlatCausal
import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Proofs.FlatFreeGain.hh7.AgeMeasureAC
import UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Assembly

/-!
# Decomposition of `zeroEntranceCausal_of` (item `PartIII-b:C/near/delta/9/1`)

Source of record `the November 2 reference manuscript`,
3541-3545 ("a homogeneous difference in the energy class ... has a sequence `δ_j ↓ 0` with
`δ_j^{-1/2}‖u(δ_j)‖² → 0` ... This also proves causality"), 3420-3440, 3561-3571.

`FreeCausalExistsUnique` only gives existence/uniqueness on the whole half-line; the causality
needs the forward energy uniqueness `FreeForwardUniqueness`: a causal zero-entrance energy solution
of the free equation whose source vanishes for ages `s < T` vanishes there.  (The truncation
`1_{s ≥ T} b` is not a causal solution: integrating `-⟨b,Φ_s⟩` by parts over `(T,∞)` leaves the
boundary term `b(T)Φ(T)`.)  Given this lemma, `zeroEntranceCausal_of_forward` below is the pure
restriction/measure bookkeeping.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Delta

open UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Short.PartIIIb.NearInst UnforcedLeray.Cons.C03.Concrete
  UnforcedLeray.Blueprint.Planar

/-- **Forward energy uniqueness on an initial age interval** (source 3541-3545, 3426-3440 with
`v = 0`): if `b` is a causal zero-entrance energy solution of the free equation whose source `F`
vanishes a.e. for ages `s < T`, then `b` vanishes a.e. on `(0,T) × cell`.  (Route: the energy
identity on `(δ, T)` for the solution, test against `b` itself via mollification in `s`; the
coercive term `ν‖∇b‖² + (Re μ) s⁻¹‖b‖²` is nonnegative, the zero-entrance condition gives
`δ_j^{-1/2}‖b(δ_j)‖² → 0`, hence `b = 0` on `(0,T)`.) -/
def FreeForwardUniqueness : Prop :=
  ∀ (c ν : ℝ) (μ : ℂ) (F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ)
    (b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ) (G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ) (T : ℝ),
    0 < c → 0 < ν → 0 ≤ μ.re → 0 < T →
    (∀ᵐ p ∂(volume.restrict (Ioi (0 : ℝ) ×ˢ UnforcedLeray.B0579.cell c)),
      p.1 < T → ∀ i j, F p i j = 0) →
    UnforcedLeray.Short.IIIa.IsCausalEnergySolution c ν μ (fun _ _ _ => 0) F b G →
    ∀ᵐ p ∂(volume.restrict (Ioi (0 : ℝ) ×ˢ UnforcedLeray.B0579.cell c)),
      p.1 < T → ∀ i, b p i = 0

theorem ageBelow_measurable (T : ℝ) : MeasurableSet (ageBelow T) :=
  measurableSet_lt measurable_fst measurable_const

theorem ageAbove_measurable (T : ℝ) : MeasurableSet (ageAbove T) :=
  measurableSet_le measurable_const measurable_fst

theorem zeroEntranceCausal_of_forward (hF : FreeForwardUniqueness) : ZeroEntranceCausal := by
  intro P hP Kset hK hKs mZ hmZ dm dp hdm
  refine ⟨1, one_pos, ?_⟩
  intro p d hreg hν ρb hρ hρ1 μ hμ S0 hS0 T hT
  have hcpos : 0 < p.c := p.c_pos
  have hμre : (0 : ℝ) ≤ ((μ : ℝ) : ℂ).re := by
    have := (hKs hμ).1
    simpa using this.le
  apply ContinuousLinearMap.ext
  intro F
  set A : Set Chart := ageAbove T with hAdef
  have hAm : MeasurableSet A := ageAbove_measurable T
  have hBm : MeasurableSet (ageBelow T) := ageBelow_measurable T
  set G := inRestr p.c mZ ρb A F with hG
  obtain ⟨b, G', hbv, hsol⟩ := hS0 G
  -- absolute continuity of the chart measures w.r.t. Lebesgue
  have hac : ∀ a, ageμ p.c a ≪
      (volume : Measure (ℝ × (ℝ × ℝ))).restrict (Ioi (0 : ℝ) ×ˢ UnforcedLeray.B0579.cell p.c) :=
    fun a => ageMeasureAC p.c a hcpos
  have hz1 : (volume : Measure (ℝ × (ℝ × ℝ))).restrict
      (Ioi (0 : ℝ) ×ˢ UnforcedLeray.B0579.cell p.c) ≪ z1Measure p.c mZ :=
    (FlatSettingInst.volCyl_ac_ageμ hcpos (-1 / 2)).trans
      (FlatSettingInst.ageμ_ac_z1Measure p.c mZ)
  have hht : (volume : Measure (ℝ × (ℝ × ℝ))).restrict
      (Ioi (0 : ℝ) ×ˢ UnforcedLeray.B0579.cell p.c) ≪ htRhoMeasure p.c ρb :=
    (FlatSettingInst.volCyl_ac_ageμ hcpos (-1 / 2)).trans
      (Measure.absolutelyContinuous_smul (ENNReal.ofReal_pos.2 (inv_pos.2 hρ)).ne')
  -- the source of the restricted input vanishes for `s < T`
  have h1 : (G.fst : Chart → Ten3) =ᵐ[z1Measure p.c mZ] ind A • (F.fst : Chart → Ten3) :=
    restrLp_ae hAm F.fst
  have h2 : (G.snd : Chart → Ten3) =ᵐ[htRhoMeasure p.c ρb] ind A • (F.snd : Chart → Ten3) :=
    restrLp_ae hAm F.snd
  have hsrc : ∀ᵐ q ∂(volume.restrict (Ioi (0 : ℝ) ×ˢ UnforcedLeray.B0579.cell p.c)),
      q.1 < T → ∀ i j, merBlockC (zsum G) q i j = 0 := by
    filter_upwards [hz1.ae_le h1, hht.ae_le h2] with q hq1 hq2 hqT i j
    have hind : ind A q = 0 := by
      have : q ∉ A := by
        simp only [hAdef, ageAbove, Set.mem_ofPred_eq, not_le]; exact hqT
      simp [ind, Set.indicator_of_notMem this]
    have e1 : (G.fst : Chart → Ten3) q = 0 := by
      rw [hq1]; simp [hind]
    have e2 : (G.snd : Chart → Ten3) q = 0 := by
      rw [hq2]; simp [hind]
    have hz : zsum G q = 0 := by simp [zsum, e1, e2]
    have hns : nsSym (0 : Ten3) = 0 := by
      ext a b
      fin_cases a <;> fin_cases b <;> simp [nsSym, symRZ]
    simp [merBlockC, hz, hns]
  have hzero := hF p.c p.ν ((μ : ℝ) : ℂ) _ b G' T hcpos p.ν_pos hμre hT hsrc hsol
  -- transfer to the velocity measure
  have hzero' : ∀ᵐ q ∂(ageμ p.c (-3 / 2)), q.1 < T → ∀ i, b q i = 0 := (hac _).ae_le hzero
  have hout : ((outRestr p.c (ageBelow T) (S0 G) : Hsp p.c) : Chart → EuclideanSpace ℝ (Fin 2))
      =ᵐ[ageμ p.c (-3 / 2)] ind (ageBelow T) • ((S0 G : Hsp p.c) : Chart → EuclideanSpace ℝ (Fin 2)) :=
    restrLp_ae hBm (S0 G)
  apply Lp.ext
  filter_upwards [hout, hbv, hzero', Lp.coeFn_zero (EuclideanSpace ℝ (Fin 2)) 2
    (ageμ p.c (-3 / 2))] with q hq1 hq2 hq3 hq4
  simp only [ContinuousLinearMap.zero_apply]
  rw [hq4]
  change ((outRestr p.c (ageBelow T) (S0 G) : Hsp p.c) : Chart → EuclideanSpace ℝ (Fin 2)) q = 0
  rw [hq1]
  change ind (ageBelow T) q • ((S0 G : Hsp p.c) : Chart → EuclideanSpace ℝ (Fin 2)) q = 0
  by_cases hq : q ∈ ageBelow T
  · have hlt : q.1 < T := hq
    have : ((S0 G : Hsp p.c) : Chart → EuclideanSpace ℝ (Fin 2)) q = 0 := by
      ext i
      have h5 := hq3 hlt i
      have h6 := hq2
      have h7 : (b q i) = (((S0 G : Hsp p.c) : Chart → EuclideanSpace ℝ (Fin 2)) q i : ℂ) := by
        rw [h6]; rfl
      rw [h5] at h7
      simpa using h7.symm
    rw [this, smul_zero]
  · simp [ind, Set.indicator_of_notMem hq]

end UnforcedLeray.Short.PartIIIb.NearInst.Delta
