import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1_3_1.ChartLift
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1_3_1.RawProf
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1_3_1.FarOrg

/-!
# Far-field jets of the raw field (task `PartIII-b:C/ward/12/3/1/2/5/1/1/3/1/4`,
target `rawFarJets : RawFarJets`)

Source `the November 2 reference manuscript`,
lines 1206-1222 (ring lift) and 2542-2546 (large-radius unprojected derivatives).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff
open UnforcedLeray.Cons.C03.Concrete (Params)

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Joint `C^∞` regularity of the ring lift `Nv R B` off the axis when `B` is `C^∞` on `s > 0`. -/
theorem contDiffOn_Nv_off_axis {R : ℝ} (hR : 0 < R)
    {B : ℝ × (ℝ × ℝ) → Axi.Merid}
    (hB : ContDiffOn ℝ ∞ B {m : ℝ × (ℝ × ℝ) | 0 < m.1}) :
    ContDiffOn ℝ ∞ (fun q : ℝ × UnforcedLeray.Space => Axi.Nv R B q.1 q.2)
      {q : ℝ × UnforcedLeray.Space | q.2 ∉ Axi.axis} := by
  have hmaps : MapsTo (fun q : ℝ × UnforcedLeray.Space => q.2)
      {q : ℝ × UnforcedLeray.Space | q.2 ∉ Axi.axis} Axi.axisᶜ :=
    fun _ hq => hq
  have hϱ : ContDiffOn ℝ ∞ (fun q : ℝ × UnforcedLeray.Space => Axi.ϱ q.2)
      {q : ℝ × UnforcedLeray.Space | q.2 ∉ Axi.axis} :=
    Axi.contDiffOn_ϱ.comp contDiff_snd.contDiffOn hmaps
  have hϱne : ∀ q ∈ {q : ℝ × UnforcedLeray.Space | q.2 ∉ Axi.axis}, Axi.ϱ q.2 ≠ 0 :=
    fun _ hq => Axi.ϱ_ne_zero hq
  have hage : ContDiffOn ℝ ∞ (fun q : ℝ × UnforcedLeray.Space => Axi.age R q.2)
      {q : ℝ × UnforcedLeray.Space | q.2 ∉ Axi.axis} := by
    unfold Axi.age
    exact contDiffOn_const.div (hϱ.pow 2) fun q hq => pow_ne_zero 2 (hϱne q hq)
  have hagepos : ∀ q ∈ {q : ℝ × UnforcedLeray.Space | q.2 ∉ Axi.axis}, Axi.age R q.2 ≠ 0 :=
    fun _ hq => (Axi.age_pos hR.ne' hq).ne'
  have hsq : ContDiffOn ℝ ∞ (fun q : ℝ × UnforcedLeray.Space => √(Axi.age R q.2))
      {q : ℝ × UnforcedLeray.Space | q.2 ∉ Axi.axis} := hage.sqrt hagepos
  have hphase : ContDiffOn ℝ ∞ (fun q : ℝ × UnforcedLeray.Space => Axi.phase R q.1 q.2)
      {q : ℝ × UnforcedLeray.Space | q.2 ∉ Axi.axis} := by
    unfold Axi.phase
    exact ((contDiffOn_const.mul contDiff_fst.contDiffOn).div_const 2).sub
      (contDiffOn_const.mul (hage.log hagepos))
  have htrans : ContDiffOn ℝ ∞ (fun q : ℝ × UnforcedLeray.Space => Axi.trans R q.2)
      {q : ℝ × UnforcedLeray.Space | q.2 ∉ Axi.axis} := by
    unfold Axi.trans
    have h2 : ContDiff ℝ ∞ (fun q : ℝ × UnforcedLeray.Space => q.2 2) :=
      (EuclideanSpace.proj (2 : Fin 3) : UnforcedLeray.Space →L[ℝ] ℝ).contDiff.comp contDiff_snd
    exact (contDiffOn_const.mul h2.contDiffOn).div hϱ hϱne
  have hchart : ContDiffOn ℝ ∞ (fun q : ℝ × UnforcedLeray.Space => Axi.chart R q.1 q.2)
      {q : ℝ × UnforcedLeray.Space | q.2 ∉ Axi.axis} :=
    hage.prodMk (hphase.prodMk htrans)
  have hmaps_chart : MapsTo (fun q : ℝ × UnforcedLeray.Space => Axi.chart R q.1 q.2)
      {q : ℝ × UnforcedLeray.Space | q.2 ∉ Axi.axis} {m : ℝ × (ℝ × ℝ) | 0 < m.1} :=
    fun _ hq => Axi.age_pos hR.ne' hq
  have hBc : ContDiffOn ℝ ∞ (fun q : ℝ × UnforcedLeray.Space => B (Axi.chart R q.1 q.2))
      {q : ℝ × UnforcedLeray.Space | q.2 ∉ Axi.axis} := hB.comp hchart hmaps_chart
  have hB0 : ContDiffOn ℝ ∞ (fun q : ℝ × UnforcedLeray.Space => B (Axi.chart R q.1 q.2) 0)
      {q : ℝ × UnforcedLeray.Space | q.2 ∉ Axi.axis} :=
    (EuclideanSpace.proj (0 : Fin 2) : Axi.Merid →L[ℝ] ℝ).contDiff.comp_contDiffOn hBc
  have hB1 : ContDiffOn ℝ ∞ (fun q : ℝ × UnforcedLeray.Space => B (Axi.chart R q.1 q.2) 1)
      {q : ℝ × UnforcedLeray.Space | q.2 ∉ Axi.axis} :=
    (EuclideanSpace.proj (1 : Fin 2) : Axi.Merid →L[ℝ] ℝ).contDiff.comp_contDiffOn hBc
  have heR : ContDiffOn ℝ ∞ (fun q : ℝ × UnforcedLeray.Space => Axi.eR q.2)
      {q : ℝ × UnforcedLeray.Space | q.2 ∉ Axi.axis} :=
    Axi.contDiffOn_eR.comp contDiff_snd.contDiffOn hmaps
  have hfr : ContDiffOn ℝ ∞
      (fun q : ℝ × UnforcedLeray.Space => Axi.frameL q.2 (B (Axi.chart R q.1 q.2)))
      {q : ℝ × UnforcedLeray.Space | q.2 ∉ Axi.axis} := by
    have : (fun q : ℝ × UnforcedLeray.Space => Axi.frameL q.2 (B (Axi.chart R q.1 q.2))) =
        fun q => B (Axi.chart R q.1 q.2) 0 • Axi.eR q.2 + B (Axi.chart R q.1 q.2) 1 • Axi.e3 :=
      funext fun _ => Axi.frameL_apply _ _
    rw [this]
    exact (hB0.smul heR).add (hB1.smul contDiffOn_const)
  exact hsq.smul hfr

/-- **Far-field jets of the raw field, homogeneity `-1`** (source 1206-1222, 2542-2546). -/
theorem rawFarJets : RawFarJets := by
  intro dm dp hdm
  obtain ⟨ν₀, hν₀, hprof⟩ := rawProfFarJet dm dp hdm
  refine ⟨ν₀, hν₀, ?_⟩
  intro p d hreg hν
  obtain ⟨hb, C, s0, M, hs0, hbd⟩ := hprof p d hreg hν
  have hν0 : 0 < p.ν := p.ν_pos
  have hε1 : p.ε ≤ 1 := by
    rw [hreg.eps_eq]
    apply Real.exp_le_one_iff.2
    have hneg : -d / p.ν < 0 := div_neg_of_neg_of_pos (by linarith [hreg.dm_pos, hreg.dm_le]) hν0
    exact hneg.le
  have hR1 : 1 ≤ p.R := (one_le_inv₀ p.ε_pos).2 hε1
  have hRpos : 0 < p.R := lt_of_lt_of_le one_pos hR1
  obtain ⟨K, hK0, hKb⟩ := chartLiftJets p.R hRpos
  set b := UnforcedLeray.Cons.C03.rawProfile p.ε p.train.v p.train.ψ
  set Cb : ℝ := max C 0
  have hCb0 : 0 ≤ Cb := le_max_right C 0
  have hCCb : C ≤ Cb := le_max_left C 0
  set R0 : ℝ := p.R / √s0 + p.R + 1
  have hsq_s0 : 0 < √s0 := Real.sqrt_pos.2 hs0
  have hR0_pos : 0 < R0 := by
    have : 0 < p.R / √s0 := div_pos hRpos hsq_s0
    linarith
  refine ⟨3 * K * Cb * p.R ^ M, R0, M + 2, hR0_pos, ?_, ?_⟩
  · have hsub : {x : ℝ × UnforcedLeray.Space | R0 < Axi.ϱ x.2} ⊆
        {x : ℝ × UnforcedLeray.Space | x.2 ∉ Axi.axis} := by
      intro x hx hax
      rw [Axi.mem_axis_iff] at hax
      have hx' : R0 < Axi.ϱ x.2 := hx
      linarith
    refine ((contDiffOn_Nv_off_axis hRpos hb).mono hsub).congr ?_
    intro x hx
    exact p.raw_eq_off_axis x.1 x.2 (hsub hx)
  · intro τ y hy k hk
    have hp : 0 < Axi.ϱ y := lt_trans hR0_pos hy
    have hyax : y ∉ Axi.axis := by
      intro h
      rw [Axi.mem_axis_iff] at h
      linarith
    have hyS : y ∈ (Axi.axisᶜ : Set UnforcedLeray.Space) := hyax
    have hRy : p.R ≤ Axi.ϱ y := by
      have : 0 < p.R / √s0 := div_pos hRpos hsq_s0
      linarith
    have hage_pos : 0 < (Axi.chart p.R τ y).1 := Axi.age_pos hRpos.ne' hyax
    have hage_le : (Axi.chart p.R τ y).1 ≤ s0 := by
      show Axi.age p.R y ≤ s0
      unfold Axi.age
      rw [div_le_iff₀ (pow_pos hp 2)]
      have h1 : p.R / √s0 < Axi.ϱ y := by linarith
      have h2 : p.R ≤ Axi.ϱ y * √s0 := ((div_lt_iff₀ hsq_s0).1 h1).le
      have h3 : p.R ^ 2 ≤ (Axi.ϱ y * √s0) ^ 2 := pow_le_pow_left₀ hRpos.le h2 2
      rwa [mul_pow, Real.sq_sqrt hs0.le, mul_comm] at h3
    have ht0 : 0 ≤ |y 2| / Axi.ϱ y := div_nonneg (abs_nonneg _) hp.le
    have h1t0 : 0 ≤ 1 + |y 2| / Axi.ϱ y := by linarith
    have h1t1 : 1 ≤ 1 + |y 2| / Axi.ϱ y := by linarith
    have hη : 1 + |(Axi.chart p.R τ y).2.2| ≤ p.R * (1 + |y 2| / Axi.ϱ y) := by
      show 1 + |Axi.trans p.R y| ≤ p.R * (1 + |y 2| / Axi.ϱ y)
      rw [Axi.trans, abs_div, abs_mul, abs_of_pos hRpos, abs_of_pos hp, mul_div_assoc]
      nlinarith
    have hηM : (1 + |(Axi.chart p.R τ y).2.2|) ^ M ≤
        p.R ^ M * (1 + |y 2| / Axi.ϱ y) ^ M := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) hη M
    have hbdk : ∀ l : ℕ, l ≤ 2 →
        ‖iteratedFDeriv ℝ l b (Axi.chart p.R τ y)‖ ≤
          Cb * p.R ^ M * (1 + |y 2| / Axi.ϱ y) ^ M := by
      intro l hl
      have h0 := hbd (Axi.chart p.R τ y) hage_pos hage_le l hl
      have h1 : C * (1 + |(Axi.chart p.R τ y).2.2|) ^ M ≤
          Cb * (1 + |(Axi.chart p.R τ y).2.2|) ^ M :=
        mul_le_mul_of_nonneg_right hCCb (by positivity)
      have h2 : Cb * (1 + |(Axi.chart p.R τ y).2.2|) ^ M ≤
          Cb * (p.R ^ M * (1 + |y 2| / Axi.ϱ y) ^ M) :=
        mul_le_mul_of_nonneg_left hηM hCb0
      calc ‖iteratedFDeriv ℝ l b (Axi.chart p.R τ y)‖
          ≤ C * (1 + |(Axi.chart p.R τ y).2.2|) ^ M := h0
        _ ≤ Cb * (p.R ^ M * (1 + |y 2| / Axi.ϱ y) ^ M) := h1.trans h2
        _ = Cb * p.R ^ M * (1 + |y 2| / Axi.ϱ y) ^ M := by ring
    have hS : ∑ l ∈ Finset.range (k + 1), ‖iteratedFDeriv ℝ l b (Axi.chart p.R τ y)‖ ≤
        3 * (Cb * p.R ^ M * (1 + |y 2| / Axi.ϱ y) ^ M) := by
      have hk3 : ((k : ℝ) + 1) ≤ 3 := by
        have : (k : ℝ) ≤ 2 := by exact_mod_cast hk
        linarith
      calc ∑ l ∈ Finset.range (k + 1), ‖iteratedFDeriv ℝ l b (Axi.chart p.R τ y)‖
          ≤ ∑ l ∈ Finset.range (k + 1), (Cb * p.R ^ M * (1 + |y 2| / Axi.ϱ y) ^ M) :=
            Finset.sum_le_sum (fun l hl => hbdk l (by have := Finset.mem_range.1 hl; omega))
        _ = ((k : ℝ) + 1) * (Cb * p.R ^ M * (1 + |y 2| / Axi.ϱ y) ^ M) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            push_cast
            ring
        _ ≤ 3 * (Cb * p.R ^ M * (1 + |y 2| / Axi.ϱ y) ^ M) :=
            mul_le_mul_of_nonneg_right hk3 (by positivity)
    have hev : p.raw τ =ᶠ[𝓝 y] Axi.Nv p.R b τ :=
      eventuallyEq_of_mem (Axi.isOpen_compl_axis.mem_nhds hyS) (fun z hz => p.raw_eq_off_axis τ z hz)
    have hD : ‖iteratedFDeriv ℝ k (p.raw τ) y‖ = ‖iteratedFDeriv ℝ k (Axi.Nv p.R b τ) y‖ := by
      rw [(hev.iteratedFDeriv ℝ k).eq_of_nhds]
    have hchart := hKb b hb τ y hRy k (by omega)
    have htk : (1 + |y 2| / Axi.ϱ y) ^ k * (1 + |y 2| / Axi.ϱ y) ^ M ≤
        (1 + |y 2| / Axi.ϱ y) ^ (M + 2) := by
      rw [← pow_add]
      exact pow_le_pow_right₀ h1t1 (by omega)
    calc ‖iteratedFDeriv ℝ k (p.raw τ) y‖
        = ‖iteratedFDeriv ℝ k (Axi.Nv p.R b τ) y‖ := hD
      _ ≤ K * Axi.ϱ y ^ (-(1 + (k : ℝ))) * (1 + |y 2| / Axi.ϱ y) ^ k *
            (3 * (Cb * p.R ^ M * (1 + |y 2| / Axi.ϱ y) ^ M)) :=
          hchart.trans (mul_le_mul_of_nonneg_left hS (by positivity))
      _ = (3 * K * Cb * p.R ^ M) * Axi.ϱ y ^ (-(1 + (k : ℝ))) *
            ((1 + |y 2| / Axi.ϱ y) ^ k * (1 + |y 2| / Axi.ϱ y) ^ M) := by
          ring
      _ ≤ (3 * K * Cb * p.R ^ M) * Axi.ϱ y ^ (-(1 + (k : ℝ))) *
            (1 + |y 2| / Axi.ϱ y) ^ (M + 2) :=
          mul_le_mul_of_nonneg_left htk (by positivity)
      _ = 3 * K * Cb * p.R ^ M *
            (Axi.ϱ y ^ (-(1 + (k : ℝ))) * (1 + |y 2| / Axi.ϱ y) ^ (M + 2)) := by
          ring

end UnforcedLeray.Short.PartIIIb.Concrete
