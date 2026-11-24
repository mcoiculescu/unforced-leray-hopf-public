import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_3_1_1_org.Leaf1Bound
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_3_1_1_org.Ext
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Leaf (a) of `PartIII-a:T21/c3/3/1/1`: the free moving propagator

Source `the November 2 reference manuscript` (SP) lines 2919-2925, 2937-2958
(`eq:short-causal-free-moving`).  The free moving evolution is defined on the `ℂ`-span of complex
cylinder data `J⁻¹ f₁ + i J⁻¹ f₂` (witnesses `Leaf1Aux.Wit`), is well defined and bounded there by the
free energy bound (`Wit.bound`, `Wit.out_ae_eq`), and extends by density and linearity
(`Ext.exists_extend_of_bound`: extension to the closure composed with the orthogonal projection).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

namespace ComplFreeRateSub

namespace Leaf1Aux

variable {ν m : ℝ} {tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))} {t₁ t₂ s₁ s₂ : ℝ}

theorem one_le_clockA (hν : 0 < ν) {s : ℝ} (hs : 0 ≤ s) : 1 ≤ clockA ν s := by
  unfold clockA
  have : 0 ≤ ν * s := mul_nonneg hν.le hs
  linarith

/-- For fixed ages, the bounded linear extension of the free moving evolution. -/
theorem exists_T (hν : 0 < ν) (hm : 0 ≤ m) (ht₁ : 0 ≤ t₁)
    (hFree : FreeEnergyHyp ν m tr t₁ t₂) (h1 : t₁ ≤ s₁) (h12 : s₁ ≤ s₂) (h2 : s₂ ≤ t₂) :
    ∃ T : MeasureTheory.Lp ℂ 2 (B0579.cellMeasure (dd ν s₁) m) →L[ℂ]
        MeasureTheory.Lp ℂ 2 (B0579.cellMeasure (dd ν s₂) m),
      (∀ W : Wit ν m tr s₁,
        ((T ((W.memLp_inp hm (one_le_clockA hν (ht₁.trans h1))).toLp W.inp) :
          MeasureTheory.Lp ℂ 2 (B0579.cellMeasure (dd ν s₂) m)) : ℝ × ℝ → ℂ)
          =ᵐ[B0579.cellMeasure (dd ν s₂) m] W.out s₂) ∧
      ∀ x, ‖T x‖ ≤ Real.exp ((normGrowthConst m + 1) * (movingZ ν s₂ - movingZ ν s₁)) * ‖x‖ := by
  classical
  have ha1 := one_le_clockA hν (ht₁.trans h1)
  have ha2 := one_le_clockA hν (ht₁.trans (h1.trans h12))
  set μ₁ := B0579.cellMeasure (dd ν s₁) m
  set μ₂ := B0579.cellMeasure (dd ν s₂) m
  set C := Real.exp ((normGrowthConst m + 1) * (movingZ ν s₂ - movingZ ν s₁)) with hCdef
  have hC : 0 ≤ C := (Real.exp_pos _).le
  let D : Submodule ℂ (MeasureTheory.Lp ℂ 2 μ₁) :=
    { carrier := {x | ∃ W : Wit ν m tr s₁, (x : ℝ × ℝ → ℂ) =ᵐ[μ₁] W.inp}
      add_mem' := by
        rintro x y ⟨W, hW⟩ ⟨W', hW'⟩
        refine ⟨W.add W', ?_⟩
        rw [Wit.inp_add]
        filter_upwards [Lp.coeFn_add x y, hW, hW'] with z h h1 h2
        rw [h, Pi.add_apply, h1, h2]
      zero_mem' := ⟨Wit.zero ν m tr s₁, by
        rw [Wit.inp_zero]
        exact Lp.coeFn_zero ℂ 2 μ₁⟩
      smul_mem' := by
        rintro c x ⟨W, hW⟩
        refine ⟨W.smul c, ?_⟩
        rw [Wit.inp_smul]
        filter_upwards [Lp.coeFn_smul c x, hW] with z h h1
        rw [h, Pi.smul_apply, smul_eq_mul, h1] }
  -- the chosen witness of an element of `D`
  let wit : D → Wit ν m tr s₁ := fun x => Classical.choose x.2
  have hwit : ∀ x : D, ((x : MeasureTheory.Lp ℂ 2 μ₁) : ℝ × ℝ → ℂ) =ᵐ[μ₁] (wit x).inp :=
    fun x => Classical.choose_spec x.2
  have hout : ∀ W : Wit ν m tr s₁, MemLp (W.out s₂) 2 μ₂ := fun W => W.memLp_out h12 hm ha2
  -- uniqueness of outputs
  have huniq : ∀ (W W' : Wit ν m tr s₁), W.inp =ᵐ[μ₁] W'.inp → W.out s₂ =ᵐ[μ₂] W'.out s₂ :=
    fun W W' h => Wit.out_ae_eq hFree W W' h1 h12 h2 hm ha1 ha2 h
  have hΦ : ∀ x : D, ∀ f : MeasureTheory.Lp ℂ 2 μ₂,
      f = (hout (wit x)).toLp ((wit x).out s₂) → (f : ℝ × ℝ → ℂ) =ᵐ[μ₂] (wit x).out s₂ := by
    intro x f hf
    rw [hf]; exact MemLp.coeFn_toLp _
  let Φ : D →ₗ[ℂ] MeasureTheory.Lp ℂ 2 μ₂ :=
    { toFun := fun x => (hout (wit x)).toLp ((wit x).out s₂)
      map_add' := by
        intro x y
        refine Lp.ext ?_
        have h3 := huniq (wit (x + y)) ((wit x).add (wit y)) (by
          rw [Wit.inp_add]
          filter_upwards [hwit (x + y), Lp.coeFn_add (x : MeasureTheory.Lp ℂ 2 μ₁) y,
            hwit x, hwit y] with z h h0 h1 h2
          rw [← h]
          erw [h0]
          rw [Pi.add_apply, h1, h2])
        filter_upwards [hΦ (x + y) _ rfl, Lp.coeFn_add
          ((hout (wit x)).toLp ((wit x).out s₂)) ((hout (wit y)).toLp ((wit y).out s₂)),
          hΦ x _ rfl, hΦ y _ rfl, h3] with z e0 e1 e2 e3 e4
        rw [e0, e1, Pi.add_apply, e2, e3, e4, Wit.out_add]
      map_smul' := by
        intro c x
        refine Lp.ext ?_
        have h3 := huniq (wit (c • x)) ((wit x).smul c) (by
          rw [Wit.inp_smul]
          filter_upwards [hwit (c • x), Lp.coeFn_smul c (x : MeasureTheory.Lp ℂ 2 μ₁),
            hwit x] with z h h0 h1
          rw [← h]
          erw [h0]
          rw [Pi.smul_apply, smul_eq_mul, h1])
        filter_upwards [hΦ (c • x) _ rfl, Lp.coeFn_smul c
          ((hout (wit x)).toLp ((wit x).out s₂)), hΦ x _ rfl, h3] with z e0 e1 e2 e4
        rw [RingHom.id_apply, e0, e1, Pi.smul_apply, smul_eq_mul, e2, e4, Wit.out_smul] }
  have hbd : ∀ x : D, ‖Φ x‖ ≤ C * ‖x‖ := by
    intro x
    have hb := Wit.bound hFree (wit x) h1 h12 h2 hm ha1 ha2
    have hxn : ‖x‖ = (xNorm (dd ν s₁) m (wit x).inp).toReal := by
      show ‖(x : MeasureTheory.Lp ℂ 2 μ₁)‖ = _
      rw [Lp.norm_def]
      congr 1
      exact eLpNorm_congr_ae (hwit x)
    have hfin : ENNReal.ofReal C * xNorm (dd ν s₁) m (wit x).inp ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        ((wit x).memLp_inp hm ha1).eLpNorm_lt_top.ne
    show ‖(hout (wit x)).toLp ((wit x).out s₂)‖ ≤ _
    rw [Lp.norm_toLp, hxn]
    calc (eLpNorm ((wit x).out s₂) 2 μ₂).toReal
        ≤ (ENNReal.ofReal C * xNorm (dd ν s₁) m (wit x).inp).toReal :=
          ENNReal.toReal_mono hfin hb
      _ = C * (xNorm (dd ν s₁) m (wit x).inp).toReal := by
          rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC]
  obtain ⟨T, hT, hTb⟩ := Ext.exists_extend_of_bound D Φ C hC hbd
  refine ⟨T, ?_, hTb⟩
  intro W
  set hW := W.memLp_inp hm ha1
  have hmem : hW.toLp W.inp ∈ D :=
    ⟨W, hW.coeFn_toLp⟩
  have hTx := hT ⟨_, hmem⟩
  have h5 := huniq (wit ⟨_, hmem⟩) W (by
    filter_upwards [hwit ⟨_, hmem⟩, hW.coeFn_toLp] with z e0 e1
    exact e0.symm.trans e1)
  have e6 := hΦ ⟨_, hmem⟩ _ rfl
  have : (T (hW.toLp W.inp) : ℝ × ℝ → ℂ) = ((Φ ⟨_, hmem⟩ : MeasureTheory.Lp ℂ 2 μ₂) :
      ℝ × ℝ → ℂ) := by
    rw [← hTx]
  rw [this]
  exact e6.trans h5

theorem movCx_zero_right (a : ℝ) (f : B0579.Plane → ℝ) :
    movCx a f (fun _ => 0) = JscaleInv a (fun x => ((f x : ℝ) : ℂ)) := by
  funext y
  simp [movCx, JscaleInv]

end Leaf1Aux

open Leaf1Aux in
/-- **Leaf (a)** (SP 2937-2958): the free energy bound on cylinder data yields a free moving
propagator `U` with `IsFreeMovingPropagator` (bounded, `ℂ`-linear, agreeing with the free cylinder
flow on real and on complex cylinder data). -/
theorem freeMovingPropagatorExists (ν m : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)))
    (t₁ t₂ : ℝ) : UnforcedLeray.Short.IIIa.ComplFreeRateSub.FreeMovingPropagatorExists ν m tr t₁ t₂ := by
  intro hm8 hν ht₁ h12 _ hFree
  classical
  have hm : 0 ≤ m := by linarith
  have hex := fun s₁ s₂ (h1 : t₁ ≤ s₁) (h12' : s₁ ≤ s₂) (h2 : s₂ ≤ t₂) =>
    exists_T (tr := tr) hν hm ht₁ hFree h1 h12' h2
  let U : ℝ → ℝ → (ℝ × ℝ → ℂ) → (ℝ × ℝ → ℂ) := fun s₂ s₁ g =>
    if h : (t₁ ≤ s₁ ∧ s₁ ≤ s₂ ∧ s₂ ≤ t₂) ∧ MemLp g 2 (B0579.cellMeasure (dd ν s₁) m) then
      ((Classical.choose (hex s₁ s₂ h.1.1 h.1.2.1 h.1.2.2)
        (h.2.toLp g) : MeasureTheory.Lp ℂ 2 (B0579.cellMeasure (dd ν s₂) m)) : ℝ × ℝ → ℂ)
    else 0
  have hU : ∀ s₁ s₂ (h1 : t₁ ≤ s₁) (h12' : s₁ ≤ s₂) (h2 : s₂ ≤ t₂) (g : ℝ × ℝ → ℂ)
      (hg : MemLp g 2 (B0579.cellMeasure (dd ν s₁) m)),
      U s₂ s₁ g = ((Classical.choose (hex s₁ s₂ h1 h12' h2) (hg.toLp g) :
        MeasureTheory.Lp ℂ 2 (B0579.cellMeasure (dd ν s₂) m)) : ℝ × ℝ → ℂ) := by
    intro s₁ s₂ h1 h12' h2 g hg
    exact dif_pos ⟨⟨h1, h12', h2⟩, hg⟩
  have hspec := fun s₁ s₂ (h1 : t₁ ≤ s₁) (h12' : s₁ ≤ s₂) (h2 : s₂ ≤ t₂) =>
    Classical.choose_spec (hex s₁ s₂ h1 h12' h2)
  -- agreement on complex data
  have hagree : ∀ s₁ s₂ (h1 : t₁ ≤ s₁) (h12' : s₁ ≤ s₂) (h2 : s₂ ≤ t₂)
      (f₁ f₂ : B0579.Plane → ℝ) (hf₁ : B0579.IsCylTest (ν ^ (-2 : ℝ)) f₁)
      (hf₂ : B0579.IsCylTest (ν ^ (-2 : ℝ)) f₂) (ω₁ ω₂ : ℝ → B0579.Plane → ℝ)
      (hω₁ : UnforcedLeray.Short.IIb.IsFreeCylFlow m tr s₁ f₁ ω₁)
      (hω₂ : UnforcedLeray.Short.IIb.IsFreeCylFlow m tr s₁ f₂ ω₂),
      U s₂ s₁ (movCx (clockA ν s₁) f₁ f₂) =ᵐ[B0579.cellMeasure (dd ν s₂) m]
        movCx (clockA ν s₂) (ω₁ s₂) (ω₂ s₂) := by
    intro s₁ s₂ h1 h12' h2 f₁ f₂ hf₁ hf₂ ω₁ ω₂ hω₁ hω₂
    let W : Wit ν m tr s₁ := ⟨f₁, f₂, ω₁, ω₂, hf₁, hf₂, hω₁, hω₂⟩
    have hW := W.memLp_inp hm (Leaf1Aux.one_le_clockA hν (ht₁.trans h1))
    show U s₂ s₁ W.inp =ᵐ[_] W.out s₂
    rw [hU s₁ s₂ h1 h12' h2 _ hW]
    exact (hspec s₁ s₂ h1 h12' h2).1 W
  refine ⟨U, ?_, ?_, ?_, ?_, ?_⟩
  · intro s₁ s₂ h1 h12' h2 g
    by_cases hg : MemLp g 2 (B0579.cellMeasure (dd ν s₁) m)
    · rw [hU s₁ s₂ h1 h12' h2 g hg]
      set T := Classical.choose (hex s₁ s₂ h1 h12' h2)
      have hb := (hspec s₁ s₂ h1 h12' h2).2 (hg.toLp g)
      have e1 : xNorm (dd ν s₂) m ((T (hg.toLp g) : MeasureTheory.Lp ℂ 2
          (B0579.cellMeasure (dd ν s₂) m)) : ℝ × ℝ → ℂ) = ‖T (hg.toLp g)‖ₑ :=
        (Lp.enorm_def _).symm
      have e2 : xNorm (dd ν s₁) m g = ‖hg.toLp g‖ₑ := by
        rw [Lp.enorm_def]
        exact (eLpNorm_congr_ae hg.coeFn_toLp).symm
      rw [e1, e2, ← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, ← ENNReal.ofReal_mul
        (Real.exp_pos _).le]
      exact ENNReal.ofReal_le_ofReal hb
    · have : U s₂ s₁ g = 0 := dif_neg (fun h => hg h.2)
      rw [this]
      simp [xNorm]
  · intro s₁ s₂ h1 h12' h2 f₀ hf₀ ω₀ hω₀
    have := hagree s₁ s₂ h1 h12' h2 f₀ (fun _ => 0) hf₀ (isCylTest_zero' _) ω₀ (fun _ _ => 0)
      hω₀ (isFreeCylFlow_zero tr s₁)
    rwa [movCx_zero_right, movCx_zero_right] at this
  · intro s₁ s₂ h1 h12' h2
    have ha1 := Leaf1Aux.one_le_clockA hν (ht₁.trans h1)
    refine ⟨fun g h hg hh => ?_, fun c g hg => ?_⟩
    · have hgh : MemLp (fun y => g y + h y) 2 (B0579.cellMeasure (dd ν s₁) m) := hg.add hh
      rw [hU s₁ s₂ h1 h12' h2 _ hgh, hU s₁ s₂ h1 h12' h2 _ hg, hU s₁ s₂ h1 h12' h2 _ hh]
      set T := Classical.choose (hex s₁ s₂ h1 h12' h2)
      have key : hgh.toLp (fun y => g y + h y) = hg.toLp g + hh.toLp h := by
        refine Lp.ext ?_
        filter_upwards [hgh.coeFn_toLp, Lp.coeFn_add (hg.toLp g) (hh.toLp h), hg.coeFn_toLp,
          hh.coeFn_toLp] with z e0 e1 e2 e3
        rw [e0, e1, Pi.add_apply, e2, e3]
      rw [key, map_add]
      exact Lp.coeFn_add _ _
    · have hcg : MemLp (fun y => c * g y) 2 (B0579.cellMeasure (dd ν s₁) m) := hg.const_mul c
      rw [hU s₁ s₂ h1 h12' h2 _ hcg, hU s₁ s₂ h1 h12' h2 _ hg]
      set T := Classical.choose (hex s₁ s₂ h1 h12' h2)
      have key : hcg.toLp (fun y => c * g y) = c • hg.toLp g := by
        refine Lp.ext ?_
        filter_upwards [hcg.coeFn_toLp, Lp.coeFn_smul c (hg.toLp g), hg.coeFn_toLp]
          with z e0 e1 e2
        rw [e0, e1, Pi.smul_apply, smul_eq_mul, e2]
      rw [key, map_smul]
      filter_upwards [Lp.coeFn_smul c (T (hg.toLp g))] with z e
      rw [e, Pi.smul_apply, smul_eq_mul]
  · intro s₁ s₂ h1 h12' h2 f₁ f₂ hf₁ hf₂ ω₁ ω₂ hω₁ hω₂
    exact hagree s₁ s₂ h1 h12' h2 f₁ f₂ hf₁ hf₂ ω₁ ω₂ hω₁ hω₂
  · intro s₁ s₂ h1 h12' h2 g hg
    rw [hU s₁ s₂ h1 h12' h2 g hg]
    exact Lp.aestronglyMeasurable _

end ComplFreeRateSub

end UnforcedLeray.Short.IIIa
