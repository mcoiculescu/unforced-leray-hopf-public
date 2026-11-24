import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.PartIIIb_C_near_masked_22
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_2.IntAll
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_1.L4
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_3_1.Sub.T8_1
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.Proofs.CartLiftIsTest.Basic

/-!
# `stripSplit_holds` (source 3996-4000)

Source of record: `the November 2 reference manuscript`, lines 3996-4000.

Route. For a box tensor `f` supported in `t ≥ e^δ l` and an output `x` in the band `l ≤ s < r`,
`fullOut f x - farOut f x = (√s)⁻¹ • merRe (-sepW (1_{t ≤ e^δ s} 𝒩f) y τ)`. The `sepW` integrand
splits into the parts `t > e^δ s` and `t ≤ e^δ s`; both are integrable because the source disk
radius `rr = R/√(e^δ l)` is below `ϱ y = R/√s`. Since `s < r`, `1_{t ≤ e^δ s} f` only sees the
input ages `t < e^δ r`, which gives the identity for `1_{t<e^δ r} f`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked

open UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Short.PartIIIb.NearInst UnforcedLeray.Short.PartIIIb.NearInst.Delta
  UnforcedLeray.Cons.C03.Concrete UnforcedLeray.Blueprint.Planar

theorem sp_chartOf_fst (R c : ℝ) (z : Space) (τ : ℝ) :
    (NearInst.chartOf R c z τ).1 = R ^ 2 / (z 0 ^ 2 + z 1 ^ 2) := by
  show R ^ 2 / NearInst.hRad z ^ 2 = _
  have hh : NearInst.hRad z ^ 2 = z 0 ^ 2 + z 1 ^ 2 :=
    Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))
  rw [hh]

theorem sp_floor_shift (X c : ℝ) (hc : 0 < c) :
    X + c - c * ⌊(X + c) / c + 1 / 2⌋ = X - c * ⌊X / c + 1 / 2⌋ := by
  have hc' : c ≠ 0 := hc.ne'
  rw [show (X + c) / c + 1 / 2 = X / c + 1 / 2 + 1 by field_simp; ring, Int.floor_add_one]
  push_cast
  ring

theorem sp_chartOf_period (R c : ℝ) (hR : 0 < R) (hc : 0 < c) (z : Space) (τ : ℝ) :
    NearInst.chartOf R c z (τ + 2 * c / R) = NearInst.chartOf R c z τ := by
  have hR' : R ≠ 0 := hR.ne'
  have hX : R * Real.log (NearInst.hRad z / R) + R * (τ + 2 * c / R) / 2 =
      (R * Real.log (NearInst.hRad z / R) + R * τ / 2) + c := by
    field_simp
    ring
  unfold NearInst.chartOf
  rw [hX, sp_floor_shift _ c hc]

theorem sp_cartLift_of_zero (R c : ℝ) (f : Chart → Ten3) (τ : ℝ) (z : Space)
    (h : f (NearInst.chartOf R c z τ) = 0) : NearInst.cartLift R c f τ z = 0 := by
  unfold NearInst.cartLift
  rw [h, Realization.cl_nsSym_zero]
  simp

theorem sp_cartLift_trunc (R c T : ℝ) (f : Chart → Ten3) (τ : ℝ) (z : Space)
    (h : (NearInst.chartOf R c z τ).1 < T) :
    NearInst.cartLift R c (truncAbove T f) τ z = NearInst.cartLift R c f τ z := by
  unfold NearInst.cartLift
  simp [truncAbove, h]

theorem sp_meas_t (R : ℝ) : Measurable fun z : Space => R ^ 2 / (z 0 ^ 2 + z 1 ^ 2) := by
  have hm0 : Measurable fun z : Space => z 0 :=
    (EuclideanSpace.proj (0 : Fin 3) : Space →L[ℝ] ℝ).continuous.measurable
  have hm1 : Measurable fun z : Space => z 1 :=
    (EuclideanSpace.proj (1 : Fin 3) : Space →L[ℝ] ℝ).continuous.measurable
  exact measurable_const.div ((hm0.pow_const 2).add (hm1.pow_const 2))

/-- Restriction of a separated source to the complement-free mask `1_{Q(z)}`. -/
theorem sp_isSepSource_mask (P rr : ℝ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ)
    (Q : Space → Prop) [DecidablePred Q] (hQ : MeasurableSet {z : Space | Q z})
    (hT : IIIa.IsSepSource P rr T) :
    IIIa.IsSepSource P rr (fun τ z => if Q z then T τ z else 0) := by
  refine
    { measurable := ?_
      periodic := ?_
      support := ?_ }
  · intro i j
    have hset : MeasurableSet {p : ℝ × Space | Q p.2} := hQ.preimage measurable_snd
    have hfun : (fun p : ℝ × Space => (if Q p.2 then T p.1 p.2 else 0) i j) =
        fun p => if Q p.2 then T p.1 p.2 i j else 0 := by
      funext p
      split_ifs <;> simp
    show Measurable fun p : ℝ × Space => (if Q p.2 then T p.1 p.2 else 0) i j
    rw [hfun]
    exact Measurable.ite hset (hT.measurable i j) measurable_const
  · intro τ z
    show (if Q z then T (τ + P) z else 0) = (if Q z then T τ z else 0)
    rw [hT.periodic]
  · intro τ z hz
    show (if Q z then T τ z else 0) = 0
    split_ifs
    · exact hT.support τ z hz
    · rfl

theorem sp_isSepSource_cartLift (R c : ℝ) (hR : 0 < R) (hc : 0 < c) (lam rr : ℝ)
    (hlam : 0 < lam) (hrr : 0 < rr) (hrel : R ^ 2 = lam * rr ^ 2)
    (f : Chart → Ten3) (hf : IsBoxTensor f) (hsupp : ∀ x, f x ≠ 0 → lam ≤ x.1) :
    IIIa.IsSepSource (2 * c / R) rr (NearInst.cartLift R c f) := by
  refine
    { measurable := ?_
      periodic := ?_
      support := ?_ }
  · intro i j
    exact T8_1.measurable_cartLift_entry R c f hf.measurable i j
  · intro τ z
    unfold NearInst.cartLift
    rw [sp_chartOf_period R c hR hc z τ]
  · intro τ z hz
    apply sp_cartLift_of_zero R c f τ z
    by_contra hne
    have h1 : lam ≤ (NearInst.chartOf R c z τ).1 := hsupp _ hne
    rw [sp_chartOf_fst] at h1
    have hz' : rr < NearInst.hRad z := hz
    have hh : NearInst.hRad z ^ 2 = z 0 ^ 2 + z 1 ^ 2 :=
      Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))
    have hsq : rr ^ 2 < NearInst.hRad z ^ 2 := by nlinarith
    rw [← hh] at h1
    have hpos : 0 < NearInst.hRad z ^ 2 := by
      have : 0 < rr ^ 2 := by positivity
      linarith
    have h2 : R ^ 2 / NearInst.hRad z ^ 2 < lam := by
      rw [div_lt_iff₀ hpos]
      linarith [mul_lt_mul_of_pos_left hsq hlam]
    linarith

theorem sp_cartLift_bdd_all (R c : ℝ) (hR : 0 < R) (s1 s2 L : ℝ) (hs1 : 0 < s1)
    (f : Chart → Ten3) (hband : ∀ p, f p ≠ 0 → s1 ≤ p.1 ∧ p.1 ≤ s2 ∧ |p.2.2| ≤ L) :
    ∃ r0 : ℝ, ∀ τ z, NearInst.cartLift R c f τ z ≠ 0 → ‖z‖ ≤ r0 := by
  obtain ⟨r, hr⟩ := Realization.cl_cartLift_bdd R⁻¹ c (inv_pos.2 hR) f s1 s2 L hs1 (by
    intro p hp
    have hf : f p ≠ 0 := by
      intro h0
      apply hp
      rw [h0, Realization.cl_tv4_zero]
    obtain ⟨a, b, d⟩ := hband p hf
    exact ⟨⟨a, b⟩, d⟩)
  refine ⟨r, fun τ z hz => ?_⟩
  have hz' := hr τ z
  simp only [inv_inv] at hz'
  exact hz' hz

theorem sp_cartLift_tn_le (R c : ℝ) (s1 s2 L B : ℝ) (f : Chart → Ten3)
    (hB : ∀ p, ‖f p‖ ≤ B) (hband : ∀ p, f p ≠ 0 → s1 ≤ p.1 ∧ p.1 ≤ s2 ∧ |p.2.2| ≤ L)
    (τ : ℝ) (z : Space) :
    IIIa.tensorNorm (NearInst.cartLift R c f τ z) ≤ |s2| * |B| := by
  refine (cartLiftFrobBound R c f τ z).trans ?_
  by_cases hf0 : f (NearInst.chartOf R c z τ) = 0
  · rw [hf0, norm_zero, mul_zero]
    positivity
  · have hs2 := (hband _ hf0).2.1
    exact mul_le_mul (hs2.trans (le_abs_self _)) ((hB _).trans (le_abs_self _))
      (norm_nonneg _) (abs_nonneg _)

theorem sp_cart_bound (R c : ℝ) (s1 s2 L B : ℝ) (hs1 : 0 < s1) (hR : 0 < R)
    (f : Chart → Ten3) (hB : ∀ p, ‖f p‖ ≤ B)
    (hband : ∀ p, f p ≠ 0 → s1 ≤ p.1 ∧ p.1 ≤ s2 ∧ |p.2.2| ≤ L) :
    ∃ r0 : ℝ, ∀ τ z, IIIa.tensorNorm (NearInst.cartLift R c f τ z) ≤
      (Metric.closedBall (0 : Space) r0).indicator (fun _ => |s2| * |B|) z := by
  obtain ⟨r0, hr0⟩ := sp_cartLift_bdd_all R c hR s1 s2 L hs1 f hband
  refine ⟨r0, fun τ z => ?_⟩
  by_cases hz : z ∈ Metric.closedBall (0 : Space) r0
  · rw [Set.indicator_of_mem hz]
    exact sp_cartLift_tn_le R c s1 s2 L B f hB hband τ z
  · rw [Set.indicator_of_notMem hz]
    have h0 : NearInst.cartLift R c f τ z = 0 := by
      by_contra hne
      apply hz
      rw [Metric.mem_closedBall, dist_zero_right]
      exact hr0 τ z hne
    rw [h0]
    simp [IIIa.tensorNorm]

theorem sp_mask_bound (r0 K : ℝ) (hK : 0 ≤ K) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ)
    (hT : ∀ τ z, IIIa.tensorNorm (T τ z) ≤ (Metric.closedBall (0 : Space) r0).indicator (fun _ => K) z)
    (Q : Space → Prop) [DecidablePred Q] (τ : ℝ) (z : Space) :
    IIIa.tensorNorm ((fun τ z => if Q z then T τ z else 0) τ z) ≤
      (Metric.closedBall (0 : Space) r0).indicator (fun _ => K) z := by
  show IIIa.tensorNorm (if Q z then T τ z else 0) ≤ _
  split_ifs with h
  · exact hT τ z
  · have h0 : IIIa.tensorNorm (0 : Matrix (Fin 3) (Fin 3) ℝ) = 0 := by
      simp [IIIa.tensorNorm]
    rw [h0]
    exact Set.indicator_nonneg (fun _ _ => hK) z

theorem sp_sepMoment_of_bdd (P : ℝ) (hP : 0 < P) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ)
    (r0 K : ℝ) (hbd : ∀ τ z, IIIa.tensorNorm (T τ z) ≤
      (Metric.closedBall (0 : Space) r0).indicator (fun _ => K) z) : SepMoment P T := by
  unfold SepMoment IIIa.ltauLq
  have hC0top : ENNReal.ofReal K ^ (2:ℝ) * volume (Metric.closedBall (0 : Space) r0) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top)
      measure_closedBall_lt_top.ne
  have hpt : ∀ τ z, IIIa.srcNorm T τ z ^ (2:ℝ) ≤
      (Metric.closedBall (0 : Space) r0).indicator (fun _ => ENNReal.ofReal K ^ (2:ℝ)) z := by
    intro τ z
    unfold IIIa.srcNorm
    have h1 := hbd τ z
    by_cases hz : z ∈ Metric.closedBall (0 : Space) r0
    · rw [Set.indicator_of_mem hz] at h1 ⊢
      exact ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal h1) (by norm_num)
    · rw [Set.indicator_of_notMem hz] at h1 ⊢
      have h0 : ENNReal.ofReal (IIIa.tensorNorm (T τ z)) = 0 := ENNReal.ofReal_eq_zero.2 h1
      rw [h0, ENNReal.zero_rpow_of_pos (by norm_num)]
  have hinner : ∀ τ : ℝ, (∫⁻ y, IIIa.srcNorm T τ y ^ (2:ℝ)) ≤
      ENNReal.ofReal K ^ (2:ℝ) * volume (Metric.closedBall (0 : Space) r0) := by
    intro τ
    calc (∫⁻ y, IIIa.srcNorm T τ y ^ (2:ℝ))
        ≤ ∫⁻ y, (Metric.closedBall (0 : Space) r0).indicator
            (fun _ => ENNReal.ofReal K ^ (2:ℝ)) y := lintegral_mono (fun y => hpt τ y)
      _ = ENNReal.ofReal K ^ (2:ℝ) * volume (Metric.closedBall (0 : Space) r0) :=
          lintegral_indicator_const measurableSet_closedBall _
  have hpow : ∀ a : ℝ≥0∞, a ^ ((2:ℝ) / 2) = a := fun a => by norm_num
  have houter : (∫⁻ τ in Ioc 0 P, (∫⁻ y, IIIa.srcNorm T τ y ^ (2:ℝ)) ^ ((2:ℝ) / 2)) ≤
      (ENNReal.ofReal K ^ (2:ℝ) * volume (Metric.closedBall (0 : Space) r0)) * ENNReal.ofReal P := by
    simp only [hpow]
    calc (∫⁻ τ in Ioc 0 P, ∫⁻ y, IIIa.srcNorm T τ y ^ (2:ℝ))
        ≤ ∫⁻ τ in Ioc 0 P, (ENNReal.ofReal K ^ (2:ℝ) * volume (Metric.closedBall (0 : Space) r0)) :=
          lintegral_mono (fun τ => hinner τ)
      _ = (ENNReal.ofReal K ^ (2:ℝ) * volume (Metric.closedBall (0 : Space) r0)) * ENNReal.ofReal P := by
          rw [setLIntegral_const, Real.volume_Ioc, sub_zero, mul_comm]
  have hfin : (ENNReal.ofReal P)⁻¹ * (∫⁻ τ in Ioc 0 P,
      (∫⁻ y, IIIa.srcNorm T τ y ^ (2:ℝ)) ^ ((2:ℝ) / 2)) ≠ ⊤ := by
    refine ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 hP).ne') ?_
    exact ne_top_of_le_ne_top (ENNReal.mul_ne_top hC0top ENNReal.ofReal_ne_top) houter
  exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hfin

theorem sp_sepMoment_cart (R c : ℝ) (hR : 0 < R) (hc : 0 < c) (s1 s2 L B : ℝ) (hs1 : 0 < s1)
    (f : Chart → Ten3) (hB : ∀ p, ‖f p‖ ≤ B)
    (hband : ∀ p, f p ≠ 0 → s1 ≤ p.1 ∧ p.1 ≤ s2 ∧ |p.2.2| ≤ L) :
    SepMoment (2 * c / R) (NearInst.cartLift R c f) := by
  obtain ⟨r0, hbd⟩ := sp_cart_bound R c s1 s2 L B hs1 hR f hB hband
  exact sp_sepMoment_of_bdd _ (by positivity) _ r0 _ hbd

theorem sp_sepPhi_add (ν : ℝ) (μ : ℂ) (T T1 T2 : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ)
    (hT : ∀ τ' z, T τ' z = T1 τ' z + T2 τ' z) (τ : ℝ) (i : Fin 3) (p : ℝ × Space) (y : Space) :
    sepPhi ν μ T τ i p y = sepPhi ν μ T1 τ i p y + sepPhi ν μ T2 τ i p y := by
  unfold sepPhi
  simp only [hT, Matrix.add_apply, Complex.ofReal_add, mul_add, Finset.sum_add_distrib]

theorem sp_merRe_neg_add (u v : Fin 3 → ℂ) : merRe (-(u + v)) = merRe (-u) + merRe (-v) := by
  ext i
  fin_cases i <;> simp [merRe] <;> ring

theorem sp_varrho_chartY (R : ℝ) (hR : 0 < R) (x : Chart) (hs : 0 < x.1) :
    UnforcedLeray.Axi.ϱ (NearInst.chartY R x) = R / Real.sqrt x.1 := by
  have hpos : 0 < Real.sqrt x.1 := Real.sqrt_pos.2 hs
  unfold UnforcedLeray.Axi.ϱ NearInst.chartY
  simp only [PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  rw [show (R / Real.sqrt x.1) ^ 2 + (0:ℝ) ^ 2 = (R / Real.sqrt x.1) ^ 2 by ring]
  exact Real.sqrt_sq (by positivity)

theorem sp_integrable (ν μ : ℝ) (hν : 0 < ν) (hμ : μ ∈ Ioo (0 : ℝ) (1 / 4)) (P rr : ℝ)
    (hP : 0 < P) (hr : 0 ≤ rr) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ)
    (hS : IIIa.IsSepSource P rr T) (hM : SepMoment P T) (τ : ℝ) (y : Space)
    (hy : rr < UnforcedLeray.Axi.ϱ y) (i : Fin 3) :
    Integrable (fun p => sepPhi ν (μ : ℂ) T τ i p y) sepRho := by
  have hμ' : -(1 / 4) < (μ : ℂ).re := by
    simp only [Complex.ofReal_re]
    linarith [hμ.1, hμ.2]
  exact sepIntegrableOfSource_all ν (μ : ℂ) rr P T hν hμ' hr hP hS hM τ y hy i

theorem sp_fullOut_sub_farOut (R c ν μ δ S l r : ℝ) (hR : 0 < R) (hc : 0 < c) (hν : 0 < ν)
    (hμ : μ ∈ Ioo (0 : ℝ) (1 / 4)) (hδ : 0 < δ) (hl : 0 < l) (hlr : l < r)
    (hrl : r ≤ Real.exp (δ / 2) * l) (hrS : r ≤ S)
    (f : Chart → Ten3) (hf : IsBoxTensor f) (hsupp : ∀ x, f x ≠ 0 → Real.exp δ * l ≤ x.1)
    (x : Chart) (hx : x ∈ ageBand l r) :
    fullOut R c ν μ f x - farOut R c ν μ δ S f x =
      (Real.sqrt x.1)⁻¹ • merRe (-IIIa.sepW ν (μ : ℂ)
        (fun τ z => if R ^ 2 / (z 0 ^ 2 + z 1 ^ 2) ≤ Real.exp δ * x.1 then
          NearInst.cartLift R c f τ z else 0)
        (NearInst.chartY R x) (NearInst.chartTau R x)) := by
  have hx' : l ≤ x.1 ∧ x.1 < r := hx
  obtain ⟨hx1, hx2⟩ := hx'
  have hs : 0 < x.1 := lt_of_lt_of_le hl hx1
  have hxS : x.1 < S := lt_of_lt_of_le hx2 hrS
  obtain ⟨s1, s2, L, hs1, hband⟩ := hf.band
  obtain ⟨B, hB⟩ := hf.bounded
  have hexp : Real.exp (δ / 2) < Real.exp δ := Real.exp_lt_exp.2 (by linarith)
  have hlt : x.1 < Real.exp δ * l := by
    have : Real.exp (δ / 2) * l < Real.exp δ * l := mul_lt_mul_of_pos_right hexp hl
    linarith
  have hlam0 : 0 < Real.exp δ * l := by positivity
  obtain ⟨rr, hrr⟩ : ∃ rr : ℝ, rr = R / Real.sqrt (Real.exp δ * l) := ⟨_, rfl⟩
  have hrr0 : 0 < rr := by rw [hrr]; positivity
  have hrel : R ^ 2 = (Real.exp δ * l) * rr ^ 2 := by
    rw [hrr, div_pow, Real.sq_sqrt hlam0.le]
    field_simp
  have hylt : rr < R / Real.sqrt x.1 := by
    rw [hrr]
    exact div_lt_div_of_pos_left hR (Real.sqrt_pos.2 hs) (Real.sqrt_lt_sqrt hs.le hlt)
  have hy : rr < UnforcedLeray.Axi.ϱ (NearInst.chartY R x) := by
    rw [sp_varrho_chartY R hR x hs]
    exact hylt
  have hP : 0 < 2 * c / R := by positivity
  have hsrc : IIIa.IsSepSource (2 * c / R) rr (NearInst.cartLift R c f) :=
    sp_isSepSource_cartLift R c hR hc (Real.exp δ * l) rr hlam0 hrr0 hrel f hf hsupp
  have hMA : SepMoment (2 * c / R) (NearInst.cartLift R c f) :=
    sp_sepMoment_cart R c hR hc s1 s2 L B hs1 f hB hband
  obtain ⟨r0, hbd⟩ := sp_cart_bound R c s1 s2 L B hs1 hR f hB hband
  have hKnn : 0 ≤ |s2| * |B| := by positivity
  have hQg : MeasurableSet {z : Space | Real.exp δ * x.1 < R ^ 2 / (z 0 ^ 2 + z 1 ^ 2)} :=
    measurableSet_lt measurable_const (sp_meas_t R)
  have hQl : MeasurableSet {z : Space | R ^ 2 / (z 0 ^ 2 + z 1 ^ 2) ≤ Real.exp δ * x.1} :=
    measurableSet_le (sp_meas_t R) measurable_const
  have hSg : IIIa.IsSepSource (2 * c / R) rr (fun τ z =>
      if Real.exp δ * x.1 < R ^ 2 / (z 0 ^ 2 + z 1 ^ 2) then NearInst.cartLift R c f τ z else 0) :=
    sp_isSepSource_mask (2 * c / R) rr (NearInst.cartLift R c f)
      (fun z => Real.exp δ * x.1 < R ^ 2 / (z 0 ^ 2 + z 1 ^ 2)) hQg hsrc
  have hSl : IIIa.IsSepSource (2 * c / R) rr (fun τ z =>
      if R ^ 2 / (z 0 ^ 2 + z 1 ^ 2) ≤ Real.exp δ * x.1 then NearInst.cartLift R c f τ z else 0) :=
    sp_isSepSource_mask (2 * c / R) rr (NearInst.cartLift R c f)
      (fun z => R ^ 2 / (z 0 ^ 2 + z 1 ^ 2) ≤ Real.exp δ * x.1) hQl hsrc
  have hMG : SepMoment (2 * c / R) (fun τ z =>
      if Real.exp δ * x.1 < R ^ 2 / (z 0 ^ 2 + z 1 ^ 2) then NearInst.cartLift R c f τ z else 0) :=
    sp_sepMoment_of_bdd _ hP _ r0 _ (sp_mask_bound r0 _ hKnn _ hbd
      (fun z => Real.exp δ * x.1 < R ^ 2 / (z 0 ^ 2 + z 1 ^ 2)))
  have hML : SepMoment (2 * c / R) (fun τ z =>
      if R ^ 2 / (z 0 ^ 2 + z 1 ^ 2) ≤ Real.exp δ * x.1 then NearInst.cartLift R c f τ z else 0) :=
    sp_sepMoment_of_bdd _ hP _ r0 _ (sp_mask_bound r0 _ hKnn _ hbd
      (fun z => R ^ 2 / (z 0 ^ 2 + z 1 ^ 2) ≤ Real.exp δ * x.1))
  have hsplit : ∀ τ' z, NearInst.cartLift R c f τ' z =
      (if Real.exp δ * x.1 < R ^ 2 / (z 0 ^ 2 + z 1 ^ 2) then NearInst.cartLift R c f τ' z else 0) +
      (if R ^ 2 / (z 0 ^ 2 + z 1 ^ 2) ≤ Real.exp δ * x.1 then NearInst.cartLift R c f τ' z else 0) := by
    intro τ' z
    by_cases h : R ^ 2 / (z 0 ^ 2 + z 1 ^ 2) ≤ Real.exp δ * x.1
    · rw [if_neg (not_lt.2 h), if_pos h, zero_add]
    · rw [if_pos (not_le.1 h), if_neg h, add_zero]
  have hsum : IIIa.sepW ν (μ : ℂ) (NearInst.cartLift R c f) (NearInst.chartY R x)
      (NearInst.chartTau R x) =
      IIIa.sepW ν (μ : ℂ) (fun τ z => if Real.exp δ * x.1 < R ^ 2 / (z 0 ^ 2 + z 1 ^ 2) then
          NearInst.cartLift R c f τ z else 0) (NearInst.chartY R x) (NearInst.chartTau R x) +
      IIIa.sepW ν (μ : ℂ) (fun τ z => if R ^ 2 / (z 0 ^ 2 + z 1 ^ 2) ≤ Real.exp δ * x.1 then
          NearInst.cartLift R c f τ z else 0) (NearInst.chartY R x) (NearInst.chartTau R x) := by
    funext i
    have iA := sp_integrable ν μ hν hμ (2 * c / R) rr hP hrr0.le (NearInst.cartLift R c f) hsrc
      hMA (NearInst.chartTau R x) (NearInst.chartY R x) hy i
    have iG := sp_integrable ν μ hν hμ (2 * c / R) rr hP hrr0.le _ hSg hMG
      (NearInst.chartTau R x) (NearInst.chartY R x) hy i
    have iL := sp_integrable ν μ hν hμ (2 * c / R) rr hP hrr0.le _ hSl hML
      (NearInst.chartTau R x) (NearInst.chartY R x) hy i
    rw [Pi.add_apply, sepW_eq_integral ν (μ : ℂ) _ (NearInst.chartTau R x) i (NearInst.chartY R x) iA,
      sepW_eq_integral ν (μ : ℂ) _ (NearInst.chartTau R x) i (NearInst.chartY R x) iG,
      sepW_eq_integral ν (μ : ℂ) _ (NearInst.chartTau R x) i (NearInst.chartY R x) iL,
      ← integral_add iG iL]
    congr 1
    funext p
    exact sp_sepPhi_add ν (μ : ℂ) _ _ _ hsplit _ i p _
  unfold fullOut farOut
  rw [if_pos hxS]
  have hfar : sepWfar ν (μ : ℂ) R δ x.1 (NearInst.cartLift R c f) (NearInst.chartY R x)
      (NearInst.chartTau R x) = IIIa.sepW ν (μ : ℂ) (fun τ z => if Real.exp δ * x.1 <
        R ^ 2 / (z 0 ^ 2 + z 1 ^ 2) then NearInst.cartLift R c f τ z else 0)
        (NearInst.chartY R x) (NearInst.chartTau R x) := rfl
  rw [hfar, hsum, sp_merRe_neg_add, smul_add]
  abel

theorem stripSplit_holds (hK : IIIa.SepKernelBounds) : StripSplit := by
  intro R c ν μ δ S l r hR hc hν hμ hδ hl hlr hrl hrS f hf hsupp x hx
  have hx' : l ≤ x.1 ∧ x.1 < r := hx
  have hgf : IsBoxTensor (truncAbove (Real.exp δ * r) f) := isBoxTensor_truncAbove _ hf
  have hgsupp : ∀ y, truncAbove (Real.exp δ * r) f y ≠ 0 → Real.exp δ * l ≤ y.1 := by
    intro y hy
    have hy' := hy
    simp only [truncAbove] at hy'
    split_ifs at hy' with h
    · exact hsupp y hy'
    · exact absurd rfl hy'
  rw [sp_fullOut_sub_farOut R c ν μ δ S l r hR hc hν hμ hδ hl hlr hrl hrS f hf hsupp x hx,
    sp_fullOut_sub_farOut R c ν μ δ S l r hR hc hν hμ hδ hl hlr hrl hrS _ hgf hgsupp x hx]
  have hmask : (fun τ z => if R ^ 2 / (z 0 ^ 2 + z 1 ^ 2) ≤ Real.exp δ * x.1 then
        NearInst.cartLift R c f τ z else 0) =
      (fun τ z => if R ^ 2 / (z 0 ^ 2 + z 1 ^ 2) ≤ Real.exp δ * x.1 then
        NearInst.cartLift R c (truncAbove (Real.exp δ * r) f) τ z else 0) := by
    funext τ z
    split_ifs with h
    · have hlt : (NearInst.chartOf R c z τ).1 < Real.exp δ * r := by
        rw [sp_chartOf_fst]
        exact lt_of_le_of_lt h (mul_lt_mul_of_pos_left hx'.2 (Real.exp_pos δ))
      exact (sp_cartLift_trunc R c _ f τ z hlt).symm
    · rfl
  rw [hmask]
