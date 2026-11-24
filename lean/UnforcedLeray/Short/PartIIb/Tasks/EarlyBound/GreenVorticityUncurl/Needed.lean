import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F6
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F4
import UnforcedLeray.Short.PartIIb.Tasks.GreenSelector.CylCoupledPairing
import UnforcedLeray.Short.PartIIb.Tasks.GreenSelector.TriangleFubini
import UnforcedLeray.Short.PartIIb.Tasks.EarlyBound.LinearBodySource

/-!
# Sub-design for `PartII-b:F6/2` (`GreenVorticityUncurl`, SP 2189–2210, 2219–2222, 2254–2268)

Source of record: `the November 2 reference manuscript` (SP), lines 2189–2210
(`short-bg:green`, `short-bg:green-bound`), 2219–2222, and 2254–2268 (`short-bg:early`).

1. **R11 Duhamel/integrability export (`MixedGreenSelectorDuhamel`, `mixedGreenSelectorDuhamel_of`)**:
   `Sub/PartII-b_F4.lean` (`PartIIbF4Aux.gen_green_operators_full`) proves internally on `[0, p.H]`
   the global propagator bound `‖U r s‖ ≤ M_U`, Bochner integrability
   `IntegrableOn (fun t => Γ_α t (f t)) (Ioc 0 p.H) volume`, exact initial lift `ω 0 = Iu 0 α`,
   and the Duhamel formula `ω s = U s 0 (ω 0) + ∫ t in Ioc 0 s, U s t (f t)`, which `MixedGreenSelector`
   (`Sub/FlatInverseDesign.lean:426`, imported by accepted `PartII-b:F4`) dropped at export.
   Without editing `FlatInverseDesign.lean` or `Sub/PartII-b_F6.lean` (R11), this file packages
   `MixedGreenSelectorDuhamel` and proves `mixedGreenSelectorDuhamel_of : DichotomyProjections → MixedGreenSelectorDuhamel`
   directly from `PartIIbF4Aux.gen_green_operators_full`, `cylCoupledPairingCLM_proof`, and
   `propagatorTriangleFubini_proof`, together with `GreenVorticityUncurlDuhamel` and
   `earlyBound_of_duhamel_leaves`.
2. **Parallel leaf propositions (`GreenVorticityUncurlNeeded`)**:
   - `SliceBiotSavartGlue` (`PartII-b:F6/2/1`): lifts a continuous zero-circulation trajectory
     `ω : ℝ → Xmc c m` on `[0, H]` via canonical `B0583.velocity` / `velGradQ` / `velGradEta`
     to jointly strongly measurable, `c`-periodic profiles `(z, zq, zη)` on `Coord` with
     `HasWeakVec` spatial derivatives and weak solenoidality on `(0, H) × ℝ²`;
   - `CylKEqBiotSavartAe` (`PartII-b:F6/2/2`): identifies `Cyl.K c w` a.e. on `B0579.cell c` with
     any `IIIa.IsBiotSavart` velocity `u` for zero-circulation `w : Xmc c m` (`m > 8`, `1 ≤ c`);
   - `GreenVorticityToVelocityEq` (`PartII-b:F6/2/3`): converts the forced coupled cylinder
     vorticity weak equation for `ω` and `IsBodySource` for `g` (with `f = curl g`) into the
     planar-solenoidal velocity equation `IsMeridionalCorrectionOn.equation` on `(0, p.H) × ℝ²`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03 UnforcedLeray.Cons.C03.Concrete UnforcedLeray.Blueprint

/-! ## 1. Duhamel-enriched Green selector (`MixedGreenSelectorDuhamel`) and proof from `F3` + `F4/1` + `F4/2` -/

/-- **Duhamel-enriched `MixedGreenSelector`** (SP 2189–2210): exports alongside `MixedGreenSelector`
the global propagator norm bound `‖U r s‖ ≤ M_U`, entrance embedding `Iu0 : E2 →L[ℝ] Xmc p.c m`,
Bochner integrability of `t ↦ Γ_α t (f t)` on `Ioc 0 p.H`, exact initial identity `ω 0 = Iu0 α`,
and Duhamel representation `ω s = U s 0 (ω 0) + ∫ t in Ioc 0 s, U s t (f t)` proved in
`Sub/PartII-b_F4.lean` (`PartIIbF4Aux.gen_green_operators_full`). -/
def MixedGreenSelectorDuhamel : Prop :=
  ∀ m : ℝ, 8 < m →
  ∀ (Sig : ℝ) (lam : ℂ) (q : Blueprint.Planar.Profile), 0 < Sig →
    Blueprint.Planar.IsGrowingEigenpair lam q →
  ∀ a' b' : ℝ, 0 < a' → a' < b' → b' < lam.re / (1 + Sig) ^ 2 →
  ∀ dm dp : ℝ, 0 < dm →
    ∃ (C_green ν₀ : ℝ), 0 < C_green ∧ 0 < ν₀ ∧
      ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ → p.ageCut = Sig → p.mode = q →
        ∃ (U : ℝ → ℝ → (Xmc p.c m →L[ℝ] Xmc p.c m))
          (Iu0 : E2 →L[ℝ] Xmc p.c m)
          (P_term : Xmc p.c m →L[ℝ] E2)
          (Piu Pic : ℝ → (Xmc p.c m →L[ℝ] Xmc p.c m))
          (G_c G_u : ℝ → ℝ → (Xmc p.c m →L[ℝ] Xmc p.c m))
          (Γ_α : ℝ → (Xmc p.c m →L[ℝ] E2))
          (M_U : ℝ),
          0 ≤ M_U ∧
          (∀ s r : ℝ, 0 ≤ s → s ≤ r → r ≤ p.H → ‖U r s‖ ≤ M_U) ∧
          (∀ α : E2,
            (Iu0 α : B0579.Plane → ℝ) =ᵐ[B0579.cellMeasure p.c m] entranceVorticityComb p α ∧
            HasZeroCirculationR p.c (Iu0 α)) ∧
          IsCoupledPropagator m p U ∧
          (∀ t ∈ Icc 0 p.H,
            (Piu t).comp (Piu t) = Piu t ∧
            Pic t = ContinuousLinearMap.id ℝ (Xmc p.c m) - Piu t ∧
            ‖Piu t‖ ≤ C_green ∧ ‖Pic t‖ ≤ C_green ∧
            ‖Γ_α t‖ ≤ C_green * Real.exp (-b' * t)) ∧
          (∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ p.H →
            (U t s).comp (Piu s) = (Piu t).comp (U t s) ∧
            (U t s).comp (Pic s) = (Pic t).comp (U t s) ∧
            G_c t s = (U t s).comp (Pic s) ∧
            (U t s).comp (G_u s t) = Piu t ∧
            ‖G_c t s‖ ≤ C_green * Real.exp (a' * (t - s)) ∧
            ‖G_u s t‖ ≤ C_green * Real.exp (-b' * (t - s))) ∧
          (∀ f : ℝ → Xmc p.c m, IntegrableOn f (Ioc 0 p.H) volume →
            (∀ᵐ t ∂volume, t ∈ Ioc 0 p.H → HasZeroCirculationR p.c (f t)) →
            let ω : ℝ → Xmc p.c m := fun s =>
              (∫ t in Ioc 0 s, G_c s t (f t)) - (∫ t in Ioc s p.H, G_u s t (f t))
            let α : E2 := ∫ t in Ioc 0 p.H, Γ_α t (f t)
            ((ω 0 : B0579.Plane → ℝ) =ᵐ[B0579.cellMeasure p.c m] entranceVorticityComb p α) ∧
            P_term (ω p.H) = 0 ∧
            (∀ s ∈ Icc 0 p.H, HasZeroCirculationR p.c (ω s)) ∧
            (∀ φ : B0579.Plane → ℝ, B0579.IsCylTest p.c φ → ∀ s ∈ Icc 0 p.H,
              ∫ x in B0579.cell p.c, ω s x * φ x =
                (∫ x in B0579.cell p.c, ω 0 x * φ x) +
                  ∫ r in (0 : ℝ)..s, ∫ x in B0579.cell p.c,
                    (cylCoupledIntegrand p.train (ω r) r φ x + f r x * φ x)) ∧
            (∀ s ∈ Icc 0 p.H,
              ‖ω s‖ + ‖α‖ ≤ C_green * Real.exp (a' * p.H) * ∫ t in Ioc 0 p.H, ‖f t‖) ∧
            IntegrableOn (fun t => Γ_α t (f t)) (Ioc 0 p.H) volume ∧
            ω 0 = Iu0 α ∧
            (∀ s ∈ Icc 0 p.H, ω s = U s 0 (ω 0) + ∫ t in Ioc 0 s, U s t (f t)))

/-- Proof of `MixedGreenSelectorDuhamel` from `DichotomyProjections` (`PartII-b:F3`) and the
accepted leaves `cylCoupledPairingCLM_proof` (`F4/1`) and `propagatorTriangleFubini_proof` (`F4/2`). -/
theorem mixedGreenSelectorDuhamel_of
    (hDP : DichotomyProjections) :
    MixedGreenSelectorDuhamel := by
  open PartIIbF4Aux in
  intro m hm Sig lam q hSig hEig a' b' ha' hab' hb' dm dp hdm
  have hm_half : 1 / 2 < m := by linarith
  obtain ⟨L₀, C_proj, ν₁, hL₀, hC_proj, hν₁, hDP_p⟩ :=
    hDP m hm Sig lam q hSig hEig a' b' ha' hab' hb' dm dp hdm
  set C_green : ℝ := 4 * C_proj ^ 5
  have hC_green_pos : 0 < C_green := by dsimp [C_green]; positivity
  set ν₀ : ℝ := min ν₁ 1
  have hν₀_pos : 0 < ν₀ := lt_min hν₁ zero_lt_one
  refine ⟨C_green, ν₀, hC_green_pos, hν₀_pos, ?_⟩
  intro p d hbg hν hAge hMode
  have hν_le_ν₁ : p.ν ≤ ν₁ := hν.trans (min_le_left _ _)
  have hν_le_1 : p.ν ≤ 1 := hν.trans (min_le_right _ _)
  have hc1 : 1 ≤ p.c := bgRegime_c_ge_one hbg hν_le_1
  obtain ⟨U, D, hU, hD⟩ := hDP_p p d hbg hν_le_ν₁ hAge hMode
  have hL_pos : 0 < D.L := lt_of_lt_of_le zero_lt_one (hL₀.trans hD.L_bounds.1)
  have hH_nonneg : 0 ≤ p.H := by rw [← hD.total_age]; positivity
  have hU_id : ∀ s ∈ Icc 0 ((D.N : ℝ) * D.L), U s s = ContinuousLinearMap.id ℝ (Xmc p.c m) := by
    rw [hD.total_age]; exact hU.id_self
  have hU_coc : ∀ s r u : ℝ, 0 ≤ s → s ≤ r → r ≤ u → u ≤ (D.N : ℝ) * D.L →
      (U u r).comp (U r s) = U u s := by
    rw [hD.total_age]; exact hU.comp_cocycle
  have hU_cont : ∀ s ∈ Icc 0 ((D.N : ℝ) * D.L), ∀ g : Xmc p.c m,
      ContinuousOn (fun r => U r s g) (Icc s ((D.N : ℝ) * D.L)) := by
    rw [hD.total_age]; exact hU.strongCont
  have hU_short : ∀ s r : ℝ, 0 ≤ s → s ≤ r → r ≤ (D.N : ℝ) * D.L → r - s ≤ D.L →
      ‖U r s‖ ≤ C_proj := by
    rw [hD.total_age]; exact hD.short_prop_norm
  obtain ⟨hU_global_bd, Piu_t, Pic_t, G_c, G_u, Γ_α, hPt, hKer, hGu0, hPuN_Gc, hInt_props⟩ :=
    @gen_green_operators_full (Xmc p.c m) E2 _ _ _ _ _ _
      D.N D.L L₀ a' b' C_proj hD.N_pos hL₀ hD.L_bounds ha' hab' hC_proj
      U D.Iu D.Pu D.Piu D.Pic D.Bn D.Mn
      hU_id hU_coc hU_cont hU_short hD.proj_rel hD.norm_bounds hD.block_inv
      hD.block_intertwine hD.forward_center_bound hD.backward_unstable_bound
  rw [hD.total_age] at hU_global_bd hPt hKer hPuN_Gc hInt_props
  set M_U : ℝ := C_proj ^ (D.N + 2)
  have hMU_nn : 0 ≤ M_U := by dsimp [M_U]; positivity
  -- Algebraic identity Γ_α t v = -(M0N (D.Pu D.N (U p.H t v))) for all t ∈ Icc 0 p.H
  obtain ⟨M0N, -, hM0N_Pu, -, -⟩ := hD.backward_unstable_bound 0 D.N (Nat.zero_le _) le_rfl
  have ht0_eq : D.t 0 = 0 := by simp [DiscreteDichotomyData.t]
  have htN_eq : D.t D.N = p.H := by simp [DiscreteDichotomyData.t, hD.total_age]
  rw [ht0_eq, htN_eq] at hM0N_Pu
  have hPu0_Iu0 : (D.Pu 0).comp (D.Iu 0) = ContinuousLinearMap.id ℝ E2 :=
    (hD.proj_rel 0 (Nat.zero_le _)).1
  have hΓ_eq_UH : ∀ t ∈ Icc 0 p.H, ∀ v : Xmc p.c m,
      Γ_α t v = -(M0N.comp (D.Pu D.N)) (U p.H t v) := by
    intro t ht v
    have hPiu_v : Piu_t t v = -(U t 0 (D.Iu 0 (Γ_α t v))) := by
      have h1 := ContinuousLinearMap.ext_iff.mp (hKer 0 t le_rfl ht.1 ht.2).2.2.2.1 v
      rw [ContinuousLinearMap.comp_apply, hGu0 t] at h1
      change (U t 0) (-((D.Iu 0) ((Γ_α t) v))) = Piu_t t v at h1
      rw [map_neg] at h1
      exact h1.symm
    have hGc_v : G_c p.H t v = U p.H t v + U p.H 0 (D.Iu 0 (Γ_α t v)) := by
      have h1 := ContinuousLinearMap.ext_iff.mp (hKer t p.H ht.1 ht.2 le_rfl).2.2.1 v
      simp only [ContinuousLinearMap.comp_apply, (hPt t ht).2.1, FunLike.coe_sub,
        Pi.sub_apply, ContinuousLinearMap.id_apply, hPiu_v, sub_neg_eq_add, map_add] at h1
      have hcoc := ContinuousLinearMap.ext_iff.mp
        (hU.comp_cocycle 0 t p.H le_rfl ht.1 ht.2 le_rfl) (D.Iu 0 (Γ_α t v))
      rw [ContinuousLinearMap.comp_apply] at hcoc
      rwa [hcoc] at h1
    have hPu_zero : D.Pu D.N (G_c p.H t v) = 0 := by
      simpa using ContinuousLinearMap.ext_iff.mp (hPuN_Gc t ht) v
    have hM0N_zero : M0N (D.Pu D.N (G_c p.H t v)) = 0 := by rw [hPu_zero, map_zero]
    rw [hGc_v, map_add, map_add] at hM0N_zero
    have hM0N_term : M0N (D.Pu D.N (U p.H 0 (D.Iu 0 (Γ_α t v)))) = Γ_α t v := by
      have h1 := ContinuousLinearMap.ext_iff.mp hM0N_Pu (D.Iu 0 (Γ_α t v))
      simp only [ContinuousLinearMap.comp_apply] at h1
      rw [h1]
      have h2 := ContinuousLinearMap.ext_iff.mp hPu0_Iu0 (Γ_α t v)
      simpa using h2
    rw [hM0N_term] at hM0N_zero
    exact eq_neg_of_add_eq_zero_right hM0N_zero
  refine ⟨U, D.Iu 0, D.Pu D.N, Piu_t, Pic_t, G_c, G_u, Γ_α, M_U,
    hMU_nn, hU_global_bd,
    fun α => ⟨hD.entrance_eq α, hD.zeroCirc_Iu 0 (Nat.zero_le _) α⟩,
    hU, ?_, ?_, ?_⟩
  · intro t ht
    obtain ⟨h1, h2, h3, h4, h5, _⟩ := hPt t ht
    exact ⟨h1, h2, h3, h4, h5⟩
  · intro s t hs hst htH
    obtain ⟨h1, h2, h3, h4, h5, h6, _⟩ := hKer s t hs hst htH
    exact ⟨h1, h2, h3, h4, h5, h6⟩
  · intro f hf hf_circ ω α
    obtain ⟨hω0_eq, hPuN_ωH, hω_norm, hω_duh⟩ := hInt_props f hf
    have hω0_eq' : ω 0 = D.Iu 0 α := hω0_eq
    have hω0_ae : (ω 0 : B0579.Plane → ℝ) =ᵐ[B0579.cellMeasure p.c m] entranceVorticityComb p α := by
      rw [hω0_eq']; exact hD.entrance_eq α
    have hΓ_int : IntegrableOn (fun t => Γ_α t (f t)) (Ioc 0 p.H) volume := by
      have hUH_int : IntegrableOn (fun t => U p.H t (f t)) (Ioc 0 p.H) volume :=
        integrableOn_propagator_apply ⟨hH_nonneg, le_rfl⟩ hMU_nn
          hU.id_self hU.comp_cocycle hU.strongCont hU_global_bd hf
      refine ((-(M0N.comp (D.Pu D.N))).integrable_comp hUH_int).congr ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact (hΓ_eq_UH t ⟨ht.1.le, ht.2⟩ (f t)).symm
    have hPiu_circ : ∀ t ∈ Icc 0 p.H, ∀ g : Xmc p.c m, HasZeroCirculationR p.c (Piu_t t g) := by
      intro t ht g
      obtain ⟨_, _, _, _, _, α_t, hPiu_eq⟩ := hPt t ht
      rw [hPiu_eq]
      have hj_lt : blkIdx D.N D.L t < D.N := blkIdx_lt hD.N_pos D.L t
      have htj_0 : 0 ≤ (blkIdx D.N D.L t : ℝ) * D.L := by positivity
      have htj_t : (blkIdx D.N D.L t : ℝ) * D.L ≤ t := blkIdx_left_le hL_pos ht.1
      exact hU.zeroCirc ((blkIdx D.N D.L t : ℝ) * D.L) t htj_0 htj_t ht.2
        (D.Iu (blkIdx D.N D.L t) (α_t g)) (hD.zeroCirc_Iu _ hj_lt.le (α_t g))
    have hGu_circ : ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ p.H →
        ∀ g : Xmc p.c m, HasZeroCirculationR p.c (G_u s t g) := by
      intro s t hs hst htH g
      obtain ⟨_, _, _, _, _, _, h7⟩ := hKer s t hs hst htH
      obtain ⟨α_g, hGu_eq⟩ := h7 g
      rw [hGu_eq]
      have hj_lt : blkIdx D.N D.L s < D.N := blkIdx_lt hD.N_pos D.L s
      have htj_0 : 0 ≤ (blkIdx D.N D.L s : ℝ) * D.L := by positivity
      have htj_s : (blkIdx D.N D.L s : ℝ) * D.L ≤ s := blkIdx_left_le hL_pos hs
      exact hU.zeroCirc ((blkIdx D.N D.L s : ℝ) * D.L) s htj_0 htj_s (hst.trans htH)
        (D.Iu (blkIdx D.N D.L s) α_g) (hD.zeroCirc_Iu _ hj_lt.le α_g)
    have hω_circ : ∀ s ∈ Icc 0 p.H, HasZeroCirculationR p.c (ω s) := by
      intro s hs
      dsimp [ω]
      refine hasZeroCirculationR_sub hm_half
        (hasZeroCirculationR_of_bochner hm_half (Ioc 0 s) measurableSet_Ioc
          (fun t => G_c s t (f t)) ?_)
        (hasZeroCirculationR_of_bochner hm_half (Ioc s p.H) measurableSet_Ioc
          (fun t => G_u s t (f t)) ?_)
      · filter_upwards [hf_circ] with t ht ht_mem
        have ht_H : t ∈ Ioc 0 p.H := ⟨ht_mem.1, ht_mem.2.trans hs.2⟩
        have hft_circ : HasZeroCirculationR p.c (f t) := ht ht_H
        have hPic_eq : Pic_t t (f t) = f t - Piu_t t (f t) := by
          rw [(hPt t ⟨ht_mem.1.le, ht_H.2⟩).2.1]; rfl
        have hPic_circ : HasZeroCirculationR p.c (Pic_t t (f t)) := by
          rw [hPic_eq]
          exact hasZeroCirculationR_sub hm_half hft_circ
            (hPiu_circ t ⟨ht_mem.1.le, ht_H.2⟩ (f t))
        rw [(hKer t s ht_mem.1.le ht_mem.2 hs.2).2.2.1]
        exact hU.zeroCirc t s ht_mem.1.le ht_mem.2 hs.2 (Pic_t t (f t)) hPic_circ
      · filter_upwards with t ht_mem
        exact hGu_circ s t hs.1 ht_mem.1.le ht_mem.2 (f t)
    refine ⟨hω0_ae, hPuN_ωH, hω_circ, ?_, hω_norm, hΓ_int, hω0_eq', hω_duh⟩
    intro φ hφ s hs
    obtain ⟨C_φ, L_φ, hC_φ, hL_φ⟩ :=
      cylCoupledPairingCLM_proof m hm p.ν p.c p.H p.train φ p.ν_pos hc1 hH_nonneg hφ
    obtain ⟨hFub_int, hFub_eq⟩ :=
      propagatorTriangleFubini_proof m hm p U M_U hc1 hH_nonneg hMU_nn hU hU_global_bd
        φ C_φ L_φ hφ hC_φ hL_φ f hf s hs
    let ω_hom : ℝ → Xmc p.c m := fun r => U r 0 (ω 0)
    let ω_inhom : ℝ → Xmc p.c m := fun r => ∫ t in Ioc 0 r, U r t (f t)
    have hU_int : ∀ r ∈ Icc 0 p.H,
        IntegrableOn (fun t => U r t (f t)) (Ioc 0 r) volume :=
      fun r hr => integrableOn_propagator_apply hr hMU_nn
        hU.id_self hU.comp_cocycle hU.strongCont hU_global_bd
        (hf.mono_set (Ioc_subset_Ioc_right hr.2))
    have hω_split : ∀ r ∈ Icc 0 p.H, ω r = ω_hom r + ω_inhom r := hω_duh
    have hweak_hom : cellTestCLM p.c m hφ (ω_hom s) =
        cellTestCLM p.c m hφ (ω 0) + ∫ r in (0 : ℝ)..s, L_φ r (ω_hom r) := by
      simp only [cellTestCLM_apply]
      rw [hU.weak φ hφ 0 s le_rfl hs.1 hs.2 (ω 0)]
      congr 1
      refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun r hr => ?_)
      rw [uIoc_of_le hs.1] at hr
      exact ((hL_φ r ⟨hr.1.le, hr.2.trans hs.2⟩).2 (ω_hom r)).2.symm
    have hint_hom : IntervalIntegrable (fun r => L_φ r (ω_hom r)) volume 0 s := by
      have h1 := hU.timeIntegrable φ hφ 0 s le_rfl hs.1 hs.2 (ω 0)
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hs.1] at h1 ⊢
      refine h1.congr_fun (fun r hr => ?_) measurableSet_Ioc
      exact ((hL_φ r ⟨hr.1.le, hr.2.trans hs.2⟩).2 (ω_hom r)).2.symm
    have hf_s : IntegrableOn f (Ioc 0 s) volume := hf.mono_set (Ioc_subset_Ioc_right hs.2)
    have htest_f_int : IntegrableOn (fun t => cellTestCLM p.c m hφ (f t)) (Ioc 0 s) volume :=
      (cellTestCLM p.c m hφ).integrable_comp hf_s
    have htest_U_int : IntegrableOn (fun t => cellTestCLM p.c m hφ (U s t (f t))) (Ioc 0 s) volume :=
      (cellTestCLM p.c m hφ).integrable_comp (hU_int s hs)
    have hpt_weak_t : ∀ t ∈ Ioc 0 s,
        cellTestCLM p.c m hφ (U s t (f t)) =
          cellTestCLM p.c m hφ (f t) + ∫ r in Ioc t s, L_φ r (U r t (f t)) := by
      intro t ht
      simp only [cellTestCLM_apply]
      rw [hU.weak φ hφ t s ht.1.le ht.2 hs.2 (f t), intervalIntegral.integral_of_le ht.2]
      congr 1
      refine setIntegral_congr_fun measurableSet_Ioc fun r hr => ?_
      exact ((hL_φ r ⟨(ht.1.trans hr.1).le, hr.2.trans hs.2⟩).2 (U r t (f t))).2.symm
    have hinner_int : IntegrableOn (fun t => ∫ r in Ioc t s, L_φ r (U r t (f t))) (Ioc 0 s) volume := by
      refine (htest_U_int.sub htest_f_int).congr_fun (fun t ht => ?_) measurableSet_Ioc
      simp only [Pi.sub_apply, hpt_weak_t t ht, add_sub_cancel_left]
    have hweak_inhom_1 : cellTestCLM p.c m hφ (ω_inhom s) =
        (∫ r in (0 : ℝ)..s, cellTestCLM p.c m hφ (f r)) +
          ∫ r in (0 : ℝ)..s, L_φ r (ω_inhom r) := by
      dsimp [ω_inhom]
      rw [← (cellTestCLM p.c m hφ).integral_comp_comm (hU_int s hs),
        setIntegral_congr_fun measurableSet_Ioc hpt_weak_t,
        integral_add htest_f_int hinner_int,
        hFub_eq, ← intervalIntegral.integral_of_le hs.1,
        ← intervalIntegral.integral_of_le hs.1]
      congr 1
      refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun r hr => ?_)
      rw [uIoc_of_le hs.1] at hr
      have hr_Icc : r ∈ Icc 0 p.H := ⟨hr.1.le, hr.2.trans hs.2⟩
      exact (L_φ r).integral_comp_comm (hU_int r hr_Icc)
    have hint_inhom : IntervalIntegrable (fun r => L_φ r (ω_inhom r)) volume 0 s := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hs.1] at hFub_int ⊢
      refine hFub_int.congr_fun (fun r hr => ?_) measurableSet_Ioc
      have hr_Icc : r ∈ Icc 0 p.H := ⟨hr.1.le, hr.2.trans hs.2⟩
      exact (L_φ r).integral_comp_comm (hU_int r hr_Icc)
    have hint_f : IntervalIntegrable (fun r => cellTestCLM p.c m hφ (f r)) volume 0 s :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hs.1).2 htest_f_int
    rw [← cellTestCLM_apply p.c m hφ (ω s), ← cellTestCLM_apply p.c m hφ (ω 0),
      hω_split s hs, map_add, hweak_hom, hweak_inhom_1]
    have hcomb :
        (cellTestCLM p.c m hφ (ω 0) + ∫ r in (0 : ℝ)..s, L_φ r (ω_hom r)) +
          ((∫ r in (0 : ℝ)..s, cellTestCLM p.c m hφ (f r)) +
            ∫ r in (0 : ℝ)..s, L_φ r (ω_inhom r)) =
        cellTestCLM p.c m hφ (ω 0) +
          ((∫ r in (0 : ℝ)..s, L_φ r (ω_hom r)) +
            (∫ r in (0 : ℝ)..s, L_φ r (ω_inhom r)) +
            (∫ r in (0 : ℝ)..s, cellTestCLM p.c m hφ (f r))) := by ring
    rw [hcomb, ← intervalIntegral.integral_add hint_hom hint_inhom,
      ← intervalIntegral.integral_add (hint_hom.add hint_inhom) hint_f]
    congr 1
    refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun r hr => ?_)
    rw [uIoc_of_le hs.1] at hr
    have hr_Icc : r ∈ Icc 0 p.H := ⟨hr.1.le, hr.2.trans hs.2⟩
    have hLr_add : L_φ r (ω_hom r) + L_φ r (ω_inhom r) = L_φ r (ω r) := by
      rw [← map_add, ← hω_split r hr_Icc]
    rw [hLr_add, ((hL_φ r hr_Icc).2 (ω r)).2, cellTestCLM_apply,
      ← integral_add ((hL_φ r hr_Icc).2 (ω r)).1 (integrableOn_mul_cylTest p.c m hφ (f r))]

/-! ## 2. Duhamel-enriched `GreenVorticityUncurlDuhamel` and `EarlyBound` assembly -/

/-- **Duhamel-enriched `GreenVorticityUncurl`** (`PartII-b:F6/2`, SP 2219–2222, 2254–2268):
same conclusion as `GreenVorticityUncurl` (`Sub/PartII-b_F6.lean:261`), receiving the Duhamel and
integrability witnesses exported by `MixedGreenSelectorDuhamel`. -/
def GreenVorticityUncurlDuhamel : Prop :=
  ∀ m : ℝ, 8 < m →
  ∀ (C_bs : ℝ) (N_bs : ℕ), 0 < C_bs →
    (∀ c : ℝ, 1 ≤ c → ∀ w : Xmc c m, HasZeroCirculationR c w →
      ∃ u uq uη : B0579.Plane → Fin 2 → ℂ,
        IIIa.IsBiotSavart c (fun x => ((w x : ℝ) : ℂ)) u ∧
        (∀ j : Fin 2, IIIa.HasWeakCellDerivC c 0 (fun x => u x j) (fun x => uq x j) ∧
          IIIa.HasWeakCellDerivC c 1 (fun x => u x j) (fun x => uη x j)) ∧
        (∑ j : Fin 2,
          (eLpNorm (fun x => u x j) 2 (volume.restrict (B0579.cell c)) +
            eLpNorm (fun x => uq x j) 2 (volume.restrict (B0579.cell c)) +
            eLpNorm (fun x => uη x j) 2 (volume.restrict (B0579.cell c)))) ≤
          ENNReal.ofReal (C_bs * c ^ N_bs * ‖w‖)) →
  ∀ (Sig : ℝ) (lam : ℂ) (q : Blueprint.Planar.Profile), 0 < Sig →
    Blueprint.Planar.IsGrowingEigenpair lam q →
  ∀ (a' b' C_green C_src C_L1 : ℝ) (k_src : ℕ),
    0 < a' → a' < b' → b' < lam.re / (1 + Sig) ^ 2 → 0 < C_green → 0 < C_src → 0 ≤ C_L1 →
  ∀ (dm dp : ℝ), 0 < dm →
  ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → 1 ≤ p.c → p.ν ≤ 1 →
    p.ageCut = Sig → p.mode = q →
    (∃ (U : ℝ → ℝ → (Xmc p.c m →L[ℝ] Xmc p.c m))
      (Iu0 : E2 →L[ℝ] Xmc p.c m)
      (P_term : Xmc p.c m →L[ℝ] E2)
      (Piu Pic : ℝ → (Xmc p.c m →L[ℝ] Xmc p.c m))
      (G_c G_u : ℝ → ℝ → (Xmc p.c m →L[ℝ] Xmc p.c m))
      (Γ_α : ℝ → (Xmc p.c m →L[ℝ] E2))
      (M_U : ℝ),
      0 ≤ M_U ∧
      (∀ s r : ℝ, 0 ≤ s → s ≤ r → r ≤ p.H → ‖U r s‖ ≤ M_U) ∧
      (∀ α : E2,
        (Iu0 α : B0579.Plane → ℝ) =ᵐ[B0579.cellMeasure p.c m] entranceVorticityComb p α ∧
        HasZeroCirculationR p.c (Iu0 α)) ∧
      IsCoupledPropagator m p U ∧
      (∀ t ∈ Icc 0 p.H,
        (Piu t).comp (Piu t) = Piu t ∧
        Pic t = ContinuousLinearMap.id ℝ (Xmc p.c m) - Piu t ∧
        ‖Piu t‖ ≤ C_green ∧ ‖Pic t‖ ≤ C_green ∧
        ‖Γ_α t‖ ≤ C_green * Real.exp (-b' * t)) ∧
      (∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ p.H →
        (U t s).comp (Piu s) = (Piu t).comp (U t s) ∧
        (U t s).comp (Pic s) = (Pic t).comp (U t s) ∧
        G_c t s = (U t s).comp (Pic s) ∧
        (U t s).comp (G_u s t) = Piu t ∧
        ‖G_c t s‖ ≤ C_green * Real.exp (a' * (t - s)) ∧
        ‖G_u s t‖ ≤ C_green * Real.exp (-b' * (t - s))) ∧
      (∀ f : ℝ → Xmc p.c m, IntegrableOn f (Ioc 0 p.H) volume →
        (∀ᵐ t ∂volume, t ∈ Ioc 0 p.H → HasZeroCirculationR p.c (f t)) →
        let ω : ℝ → Xmc p.c m := fun s =>
          (∫ t in Ioc 0 s, G_c s t (f t)) - (∫ t in Ioc s p.H, G_u s t (f t))
        let α : E2 := ∫ t in Ioc 0 p.H, Γ_α t (f t)
        ((ω 0 : B0579.Plane → ℝ) =ᵐ[B0579.cellMeasure p.c m] entranceVorticityComb p α) ∧
        P_term (ω p.H) = 0 ∧
        (∀ s ∈ Icc 0 p.H, HasZeroCirculationR p.c (ω s)) ∧
        (∀ φ : B0579.Plane → ℝ, B0579.IsCylTest p.c φ → ∀ s ∈ Icc 0 p.H,
          ∫ x in B0579.cell p.c, ω s x * φ x =
            (∫ x in B0579.cell p.c, ω 0 x * φ x) +
              ∫ r in (0 : ℝ)..s, ∫ x in B0579.cell p.c,
                (cylCoupledIntegrand p.train (ω r) r φ x + f r x * φ x)) ∧
        (∀ s ∈ Icc 0 p.H,
          ‖ω s‖ + ‖α‖ ≤ C_green * Real.exp (a' * p.H) * ∫ t in Ioc 0 p.H, ‖f t‖) ∧
        IntegrableOn (fun t => Γ_α t (f t)) (Ioc 0 p.H) volume ∧
        ω 0 = Iu0 α ∧
        (∀ s ∈ Icc 0 p.H, ω s = U s 0 (ω 0) + ∫ t in Ioc 0 s, U s t (f t)))) →
    ∀ (b0Of b0qOf b0ηOf gOf gqOf gηOf : HpR p.c →ₗ[ℝ] CProf)
      (curlSourceOf : HpR p.c →ₗ[ℝ] (ℝ → Xmc p.c m)),
      (∀ F : HpR p.c,
        InFlatClass p.c bgp (b0Of F) ∧
        IsFlatResponse p.ν 0 (toProf p.c F) (b0Of F) ∧
        HasWeakVec vQ0 dZero (b0Of F) (b0qOf F) ∧
        HasWeakVec vEta dZero (b0Of F) (b0ηOf F) ∧
        QPeriodic p.c (gOf F) ∧
        HasWeakVec vQ0 dZero (gOf F) (gqOf F) ∧
        HasWeakVec vEta dZero (gOf F) (gηOf F) ∧
        IsBodySource p.train (b0Of F) (b0qOf F) (b0ηOf F) (gOf F) ∧
        Measurable (sliceH1Norm p.c (gOf F) (gqOf F) (gηOf F)) ∧
        sLpNorm (13 / 8) p.H (sliceH1Norm p.c (gOf F) (gqOf F) (gηOf F)) ≤
          ENNReal.ofReal (C_src * (p.ν ^ k_src)⁻¹ * ‖F‖) ∧
        IntegrableOn (curlSourceOf F) (Ioc 0 p.H) volume ∧
        (∀ᵐ t ∂volume, t ∈ Ioc 0 p.H → HasZeroCirculationR p.c (curlSourceOf F t)) ∧
        (∀ᵐ s ∂volume, s ∈ Ioc 0 p.H →
          ∀ᵐ x ∂volume, x ∈ B0579.cell p.c →
            ((curlSourceOf F s x : ℝ) : ℂ) = profCurl (gqOf F) (gηOf F) (s, x)) ∧
        ∫ t in Ioc 0 p.H, ‖curlSourceOf F t‖ ≤ C_L1 * ‖F‖) →
      ∃ (αMap : HpR p.c →L[ℝ] E2)
        (zOf zqOf zηOf : HpR p.c →ₗ[ℝ] CProf),
        ∀ F : HpR p.c,
          IsMeridionalCorrectionOn p p.H (gOf F) (zOf F) (zqOf F) (zηOf F) (αMap F) ∧
          Measurable (sliceH1Norm p.c (zOf F) (zqOf F) (zηOf F)) ∧
          ∀ s ∈ Ioc 0 p.H,
            sliceH1Norm p.c (zOf F) (zqOf F) (zηOf F) s + ENNReal.ofReal ‖αMap F‖ ≤
              ENNReal.ofReal
                ((C_bs * p.c ^ N_bs + 1) * C_green * Real.exp (a' * p.H) * C_L1 * ‖F‖)

/-- **Conditional assembly of `EarlyBound` (`PartII-b:F6`)** from `GreenVorticityUncurlDuhamel`,
`DichotomyProjections` (`PartII-b:F3`, via `mixedGreenSelectorDuhamel_of`), and `BodySourceBound`
(`PartII-b:F5`, via accepted `linearBodySourceMap_proof`). -/
theorem earlyBound_of_duhamel_leaves
    (hUncurl : GreenVorticityUncurlDuhamel)
    (hDP : DichotomyProjections)
    (hBS : BodySourceBound) :
    EarlyBound := by
  have hGS := mixedGreenSelectorDuhamel_of hDP
  refine ⟨cylinderBiotSavartH1_proof, ?_⟩
  intro m hm Sig lam q hSig hEig a' ha'0 ha'lam dm dp hdm
  obtain ⟨C_bs, N_bs, hC_bs, hbs⟩ := cylinderBiotSavartH1_proof m hm
  set b' : ℝ := (a' + lam.re / (1 + Sig) ^ 2) / 2
  have hb'1 : a' < b' := by dsimp [b']; linarith
  have hb'2 : b' < lam.re / (1 + Sig) ^ 2 := by dsimp [b']; linarith
  obtain ⟨C_green, ν_g, hC_green, hν_g, hGS_p⟩ :=
    hGS m hm Sig lam q hSig hEig a' b' ha'0 hb'1 hb'2 dm dp hdm
  obtain ⟨C_src, k_src, ν_s, hC_src, hν_s, hSrc_p⟩ :=
    linearBodySourceMap_proof hBS m hm Sig lam q hSig hEig dm dp hdm
  set C_early : ℝ :=
    C_src + (C_bs + 1) * C_green * (14 ^ (7 / 11 : ℝ) * Sig ^ (1 / 22 : ℝ)) * C_src
  have hC_early : 0 < C_early := by positivity
  set k_early : ℕ := k_src + 1 + 2 * N_bs
  set ν₀ : ℝ := min (min ν_g ν_s) 1
  have hν₀ : 0 < ν₀ := lt_min (lt_min hν_g hν_s) one_pos
  refine ⟨C_early, k_early, ν₀, hC_early, hν₀, ?_⟩
  intro p d hreg hν hSig_p hmode_p
  have hν_g' : p.ν ≤ ν_g := hν.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hν_s' : p.ν ≤ ν_s := hν.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hν1 : p.ν ≤ 1 := hν.trans (min_le_right _ _)
  have hν0 : 0 < p.ν := p.ν_pos
  have hc1 : 1 ≤ p.c := one_le_c_of_nu_le_one hreg hν1
  obtain ⟨b0Of, b0qOf, b0ηOf, gOf, gqOf, gηOf, curlSourceOf, hSrc_F⟩ :=
    hSrc_p p d hreg hν_s' hν1 hSig_p hmode_p
  set C_L1 : ℝ :=
    (14 ^ (7 / 11 : ℝ) * Sig ^ (1 / 22 : ℝ) * p.ν⁻¹) * (C_src * (p.ν ^ k_src)⁻¹)
  have hC_L1 : 0 ≤ C_L1 := by dsimp [C_L1]; positivity
  obtain ⟨αMap, zOf, zqOf, zηOf, hUnc_F⟩ :=
    hUncurl m hm C_bs N_bs hC_bs hbs Sig lam q hSig hEig a' b' C_green C_src C_L1 k_src
      ha'0 hb'1 hb'2 hC_green hC_src hC_L1 dm dp hdm p d hreg hc1 hν1 hSig_p hmode_p
      (hGS_p p d hreg hν_g' hSig_p hmode_p)
      b0Of b0qOf b0ηOf gOf gqOf gηOf curlSourceOf hSrc_F
  refine ⟨αMap, b0Of, b0qOf, b0ηOf, gOf, gqOf, gηOf, zOf, zqOf, zηOf, fun F => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h10, hg_lp, _, _, _, _⟩ := hSrc_F F
  obtain ⟨h9, h11, hz_sup⟩ := hUnc_F F
  have hpow_le : ∀ a b : ℕ, a ≤ b → (p.ν ^ a)⁻¹ ≤ (p.ν ^ b)⁻¹ := by
    intro a b hab
    exact inv_anti₀ (pow_pos hν0 b) (pow_le_pow_of_le_one hν0.le hν1 hab)
  have hC_src_le : C_src ≤ C_early := by
    dsimp [C_early]
    have : 0 ≤ (C_bs + 1) * C_green * (14 ^ (7 / 11 : ℝ) * Sig ^ (1 / 22 : ℝ)) * C_src := by
      positivity
    linarith
  have hg_lp' : sLpNorm (13 / 8) p.H (sliceH1Norm p.c (gOf F) (gqOf F) (gηOf F)) ≤
      ENNReal.ofReal (C_early * (p.ν ^ k_early)⁻¹ * ‖F‖) := by
    refine hg_lp.trans (ENNReal.ofReal_le_ofReal ?_)
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg F)
    exact mul_le_mul hC_src_le (hpow_le k_src k_early (by omega)) (by positivity) hC_early.le
  refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, hg_lp', fun s hs => ?_⟩
  refine (hz_sup s hs).trans (ENNReal.ofReal_le_ofReal ?_)
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg F)
  have hc_pow : C_bs * p.c ^ N_bs + 1 ≤ (C_bs + 1) * (p.ν ^ (2 * N_bs))⁻¹ := by
    rw [c_pow_eq_inv_nu_pow hreg N_bs]
    have h1_le : (1 : ℝ) ≤ (p.ν ^ (2 * N_bs))⁻¹ := by
      simpa using hpow_le 0 (2 * N_bs) (Nat.zero_le _)
    nlinarith [hC_bs]
  have hcoef_le : (C_bs + 1) * C_green * (14 ^ (7 / 11 : ℝ) * Sig ^ (1 / 22 : ℝ)) * C_src ≤
      C_early := by
    dsimp [C_early]; linarith
  have hnu_prod :
      (p.ν ^ (2 * N_bs))⁻¹ * p.ν⁻¹ * (p.ν ^ k_src)⁻¹ = (p.ν ^ k_early)⁻¹ := by
    dsimp [k_early]
    rw [pow_add, pow_add, pow_one, mul_inv, mul_inv]
    ring
  calc (C_bs * p.c ^ N_bs + 1) * C_green * Real.exp (a' * p.H) * C_L1
      = (C_bs * p.c ^ N_bs + 1) * C_green * Real.exp (a' * p.H) *
          (14 ^ (7 / 11 : ℝ) * Sig ^ (1 / 22 : ℝ) * p.ν⁻¹) * (C_src * (p.ν ^ k_src)⁻¹) := by
        dsimp [C_L1]; ring
    _ ≤ ((C_bs + 1) * (p.ν ^ (2 * N_bs))⁻¹) * C_green * Real.exp (a' * p.H) *
          (14 ^ (7 / 11 : ℝ) * Sig ^ (1 / 22 : ℝ) * p.ν⁻¹) * (C_src * (p.ν ^ k_src)⁻¹) := by
        gcongr
    _ = ((C_bs + 1) * C_green * (14 ^ (7 / 11 : ℝ) * Sig ^ (1 / 22 : ℝ)) * C_src) *
          ((p.ν ^ (2 * N_bs))⁻¹ * p.ν⁻¹ * (p.ν ^ k_src)⁻¹) * Real.exp (a' * p.H) := by
        ring
    _ = ((C_bs + 1) * C_green * (14 ^ (7 / 11 : ℝ) * Sig ^ (1 / 22 : ℝ)) * C_src) *
          (p.ν ^ k_early)⁻¹ * Real.exp (a' * p.H) := by
        rw [hnu_prod]
    _ ≤ C_early * (p.ν ^ k_early)⁻¹ * Real.exp (a' * p.H) := by
        gcongr

/-! ## 3. Leaf propositions for `GreenVorticityUncurlDuhamel` (`PartII-b:F6/2/1..3`) -/

namespace GreenVorticityUncurlNeeded

/-- **Leaf 1 (`PartII-b:F6/2/1`, `SliceBiotSavartGlue`, SP 2258–2268)**:
given a continuous zero-circulation trajectory `ω : ℝ → Xmc c m` (`8 < m`, `1 ≤ c`, `0 < H`) on
`Icc 0 H`, the canonical cylinder Biot–Savart triple
`(B0583.velocity c hm1 (ω s) _, B0583.velGradQ c hm1 (ω s), B0583.velGradEta c hm1 (ω s) _)` lifts
(by `Infra.JointMeasurableRep.exists_stronglyMeasurable_rep` on `(0, H]` and `c`-periodic extension
in `q`, extended by `0` outside `Ioc 0 H`) to jointly strongly measurable, `c`-periodic profiles
`z, zq, zη : CProf` on `Coord` satisfying `HasWeakVec vQ0 dZero z zq`, `HasWeakVec vEta dZero z zη`,
weak solenoidality on `Ioo 0 H ×ˢ univ`, and slicewise a.e. agreement on `B0579.cell c` at every
`s ∈ Ioc 0 H`. -/
def SliceBiotSavartGlue : Prop :=
  ∀ (m : ℝ) (hm : 8 < m) (c H : ℝ) (hc1 : 1 ≤ c) (_hH : 0 < H)
    (ω : ℝ → Xmc c m) (_hω_cont : ContinuousOn ω (Icc 0 H))
    (hω_circ : ∀ s ∈ Icc 0 H, HasZeroCirculationR c (ω s)),
    haveI : Fact (0 < c) := ⟨by linarith⟩
    ∃ z zq zη : CProf,
      StronglyMeasurable z ∧ StronglyMeasurable zq ∧ StronglyMeasurable zη ∧
      QPeriodic c z ∧ QPeriodic c zq ∧ QPeriodic c zη ∧
      HasWeakVec vQ0 dZero z zq ∧
      HasWeakVec vEta dZero z zη ∧
      (∀ φ : Coord → ℝ, IsCoordTest φ → tsupport φ ⊆ Ioo 0 H ×ˢ univ →
        Integrable (fun x => z x 0 * (cpd 1 φ x : ℂ) + z x 1 * (cpd 2 φ x : ℂ)) ∧
          ∫ x, (z x 0 * (cpd 1 φ x : ℂ) + z x 1 * (cpd 2 φ x : ℂ)) = 0) ∧
      ∀ s : ℝ, ∀ hs : s ∈ Ioc 0 H,
        (fun x => z (s, x)) =ᵐ[volume.restrict (B0579.cell c)]
          (fun x => WithLp.toLp 2 fun j =>
            (B0583.velocity c (by linarith : (1 : ℝ) ≤ m) (ω s)
              (hω_circ s ⟨hs.1.le, hs.2⟩).2 : B0579.Plane → B0581.Vel) x j) ∧
        (fun x => zq (s, x)) =ᵐ[volume.restrict (B0579.cell c)]
          (fun x => WithLp.toLp 2 fun j =>
            (B0583.velGradQ c (by linarith : (1 : ℝ) ≤ m) (ω s) :
              B0579.Plane → B0581.Vel) x j) ∧
        (fun x => zη (s, x)) =ᵐ[volume.restrict (B0579.cell c)]
          (fun x => WithLp.toLp 2 fun j =>
            (B0583.velGradEta c (by linarith : (1 : ℝ) ≤ m) (ω s)
              (hω_circ s ⟨hs.1.le, hs.2⟩).2 : B0579.Plane → B0581.Vel) x j)

/-- **Leaf 2 (`PartII-b:F6/2/2`, `CylKEqBiotSavartAe`, SP 2081–2084, 2258–2262)**:
for `8 < m`, `1 ≤ c`, and `w : Xmc c m` with zero total circulation (`HasZeroCirculationR c w`),
the periodic-kernel cylinder Biot–Savart velocity `Cyl.K c w` agrees `volume.restrict (B0579.cell c)`-a.e.
with any `IIIa.IsBiotSavart c (fun x => ((w x : ℝ) : ℂ)) u` velocity `u`. -/
def CylKEqBiotSavartAe : Prop :=
  ∀ m : ℝ, 8 < m →
  ∀ c : ℝ, 1 ≤ c →
  ∀ w : Xmc c m, HasZeroCirculationR c w →
  ∀ u : B0579.Plane → Fin 2 → ℂ,
    IIIa.IsBiotSavart c (fun x => ((w x : ℝ) : ℂ)) u →
    (fun x (j : Fin 2) => ((UnforcedLeray.Cyl.K c w x j : ℝ) : ℂ)) =ᵐ[volume.restrict (B0579.cell c)] u

/-- **Leaf 3 (`PartII-b:F6/2/3`, `GreenVorticityToVelocityEq`, SP 2216–2222, 2258–2268)**:
for a parameter point `p` in `BgRegime p d dm dp` (`1 ≤ p.c`, `0 < p.H`), if `ω : ℝ → Xmc p.c m`
solves the weak forced coupled cylinder vorticity equation on `Icc 0 p.H` with source `f`,
`(z, zq, zη)` is a `c`-periodic strongly measurable `H¹`-bounded Biot–Savart uncurl of `ω` on
`(0, p.H]` agreeing a.e. on `B0579.cell p.c` with `Cyl.K p.c (ω s)`, and `g` is a `c`-periodic body
source with weak curl `f`, then `(z, zq, zη)` satisfies `IsMeridionalCorrectionOn.equation` against
every `IsPlanarSolTest Ψ` supported in `Ioo 0 p.H ×ˢ univ`. -/
def GreenVorticityToVelocityEq : Prop :=
  ∀ m : ℝ, 8 < m →
  ∀ (p : Params) (d dm dp : ℝ), BgRegime p d dm dp → 1 ≤ p.c → 0 < p.H →
  ∀ (ω f : ℝ → Xmc p.c m),
    ContinuousOn ω (Icc 0 p.H) →
    IntegrableOn f (Ioc 0 p.H) volume →
    (∀ s ∈ Icc 0 p.H, HasZeroCirculationR p.c (ω s)) →
    (∀ φ : B0579.Plane → ℝ, B0579.IsCylTest p.c φ → ∀ s ∈ Icc 0 p.H,
      ∫ x in B0579.cell p.c, ω s x * φ x =
        (∫ x in B0579.cell p.c, ω 0 x * φ x) +
          ∫ r in (0 : ℝ)..s, ∫ x in B0579.cell p.c,
            (cylCoupledIntegrand p.train (ω r) r φ x + f r x * φ x)) →
  ∀ (z zq zη : CProf),
    StronglyMeasurable z → StronglyMeasurable zq → StronglyMeasurable zη →
    QPeriodic p.c z → QPeriodic p.c zq → QPeriodic p.c zη →
    HasWeakVec vQ0 dZero z zq →
    HasWeakVec vEta dZero z zη →
    (∀ φ : Coord → ℝ, IsCoordTest φ → tsupport φ ⊆ Ioo 0 p.H ×ˢ univ →
      Integrable (fun x => z x 0 * (cpd 1 φ x : ℂ) + z x 1 * (cpd 2 φ x : ℂ)) ∧
        ∫ x, (z x 0 * (cpd 1 φ x : ℂ) + z x 1 * (cpd 2 φ x : ℂ)) = 0) →
    (∃ M : ℝ, ∀ s ∈ Ioc 0 p.H, sliceH1Norm p.c z zq zη s ≤ ENNReal.ofReal M) →
    (∀ s ∈ Ioc 0 p.H,
      IIIa.IsBiotSavart p.c (fun x => ((ω s x : ℝ) : ℂ)) (fun x j => z (s, x) j) ∧
      (∀ j : Fin 2,
        IIIa.HasWeakCellDerivC p.c 0 (fun x => z (s, x) j) (fun x => zq (s, x) j) ∧
        IIIa.HasWeakCellDerivC p.c 1 (fun x => z (s, x) j) (fun x => zη (s, x) j)) ∧
      (fun x (j : Fin 2) => ((UnforcedLeray.Cyl.K p.c (ω s) x j : ℝ) : ℂ)) =ᵐ[
          volume.restrict (B0579.cell p.c)]
        (fun x j => z (s, x) j)) →
  ∀ (b0 b0q b0η g gq gη : CProf),
    InFlatClass p.c bgp b0 →
    QPeriodic p.c g →
    HasWeakVec vQ0 dZero g gq →
    HasWeakVec vEta dZero g gη →
    IsBodySource p.train b0 b0q b0η g →
    Measurable (sliceH1Norm p.c g gq gη) →
    sLpNorm (13 / 8) p.H (sliceH1Norm p.c g gq gη) < ⊤ →
    (∀ᵐ s ∂volume, s ∈ Ioc 0 p.H →
      ∀ᵐ x ∂volume, x ∈ B0579.cell p.c →
        ((f s x : ℝ) : ℂ) = profCurl gq gη (s, x)) →
  ∀ Ψ : Coord → Fin 2 → ℝ, IsPlanarSolTest Ψ →
    (∀ i, tsupport (fun x => Ψ x i) ⊆ Ioo 0 p.H ×ˢ univ) →
    Integrable (fun x => ∑ i : Fin 2, z x i * meridTranspose p.ν Ψ x i) ∧
      Integrable (cdot (flatBv p.train z zq zη) Ψ) ∧
      Integrable (cdot g Ψ) ∧
      ∫ x, (∑ i : Fin 2, z x i * meridTranspose p.ν Ψ x i +
          cdot (flatBv p.train z zq zη) Ψ x) =
        ∫ x, cdot g Ψ x

end GreenVorticityUncurlNeeded

end UnforcedLeray.Short.IIb

end
