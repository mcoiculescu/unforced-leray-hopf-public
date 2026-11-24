import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N01_9_1_2_4_1
import UnforcedLeray.Short.PartIIa.Sub.N01.HeatInt.SlabDivZero.Bump
import UnforcedLeray.Short.PartIIa.Sub.N01.HeatInt.SlabDivZero.Fundamental

/-!
# `PartII-a:N01/9/1/2/4/1/c`: the weak equation gives the classical slab divergence

Source `the November 2 reference manuscript`
lines 1650-1658, 1684-1689, 3379-3383, 3426-3430.  If `∫ ⟪cgrad 0 Φ, F⟫ dμ_H = 0` for all profile
tests `Φ`, then every slice `F(σ,·)` of a smooth periodic force is classically divergence free.
The box case is `slabDivFundamental` (with the periodic bump `periodicBumpTest` supplying the
test functions); `σ ≤ 0` is trivial, and the rest is continuity and `q`-periodicity.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIa.N01

open UnforcedLeray.B0220 (Profile HSpace measureH cellMeasure weightH cell)
open UnforcedLeray.B0223 (MeridC)
open UnforcedLeray.B0226 (ProfileTest IsProfileTest)

/-- The complex pairing with a real profile gradient, in coordinates. -/
theorem swk_inner_cgrad (Φ : Profile → ℝ) (F : Profile → MeridC) (p : Profile) :
    @inner ℂ _ _ (UnforcedLeray.Short.PartIIa.cgrad 0 Φ p) (F p) =
      ((UnforcedLeray.Axi.dQ Φ p : ℝ) : ℂ) * F p 0 +
        ((UnforcedLeray.Axi.dEta Φ p : ℝ) : ℂ) * F p 1 := by
  unfold UnforcedLeray.Short.PartIIa.cgrad
  rw [UnforcedLeray.B0226.Deps_zero]
  simp [PiLp.inner_apply, RCLike.inner_apply, Fin.sum_univ_two, mul_comm]

/-- The cell set `Ioi 0 ×ˢ Ioc 0 c ×ˢ univ` is measurable. -/
theorem swk_measurableSet_cell (c : ℝ) : MeasurableSet (cell c) :=
  measurableSet_Ioi.prod (measurableSet_Ioc.prod MeasurableSet.univ)

/-- The cell and the open box agree up to a null set (the face `q = c`). -/
theorem swk_cell_ae_box (c : ℝ) :
    cell c =ᵐ[volume] (Ioi (0:ℝ) ×ˢ (Ioo (0:ℝ) c ×ˢ (univ : Set ℝ))) := by
  have hsing : (volume : Measure (ℝ × ℝ)) ({c} ×ˢ (univ : Set ℝ)) = 0 := by
    rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_singleton, zero_mul]
  have hnull : (volume : Measure Profile) (Ioi (0:ℝ) ×ˢ ({c} ×ˢ (univ : Set ℝ))) = 0 := by
    rw [Measure.volume_eq_prod, Measure.prod_prod, hsing, mul_zero]
  rw [ae_eq_set]
  constructor
  · refine measure_mono_null ?_ hnull
    rintro ⟨a, q, η⟩ ⟨⟨ha, ⟨hq0, hqc⟩, -⟩, hn⟩
    have hqeq : q = c := by
      by_contra hne
      exact hn ⟨ha, ⟨hq0, lt_of_le_of_ne hqc hne⟩, trivial⟩
    exact ⟨ha, hqeq, trivial⟩
  · apply measure_mono_null _ (measure_empty (μ := (volume : Measure Profile)))
    rintro ⟨a, q, η⟩ ⟨⟨ha, ⟨hq0, hqc⟩, -⟩, hn⟩
    exact (hn ⟨ha, ⟨hq0, hqc.le⟩, trivial⟩).elim

/-- The weighted cell integral of the pairing equals the box integral form. -/
theorem swk_measureH_eq (c : ℝ) (Φ : Profile → ℝ) (F : Profile → MeridC) :
    ∫ p, @inner ℂ _ _ (UnforcedLeray.Short.PartIIa.cgrad 0 Φ p) (F p) ∂(measureH c) =
      ∫ p in cell c, (((p.1 ^ (-(3/2:ℝ)) : ℝ) : ℂ) *
        (((UnforcedLeray.Axi.dQ Φ p : ℝ) : ℂ) * F p 0 +
          ((UnforcedLeray.Axi.dEta Φ p : ℝ) : ℂ) * F p 1)) := by
  unfold measureH cellMeasure
  rw [integral_withDensity_eq_integral_toReal_smul]
  · apply integral_congr_ae
    filter_upwards [ae_restrict_mem (swk_measurableSet_cell c)] with p hp
    have hp0 : (0:ℝ) < p.1 := hp.1
    simp only [weightH]
    rw [ENNReal.toReal_ofReal (Real.rpow_nonneg hp0.le _), Complex.real_smul,
      swk_inner_cgrad]
  · unfold weightH
    exact ENNReal.measurable_ofReal.comp (Measurable.pow_const measurable_fst _)
  · exact ae_of_all _ (fun x => by unfold weightH; exact ENNReal.ofReal_lt_top)

/-- Translating the first profile coordinate by `c` preserves the derivative of a periodic
function on `ℝ × ℝ`. -/
theorem swk_fderiv_shift (c : ℝ) (G : ℝ × ℝ → ℂ)
    (hG : ∀ x : ℝ × ℝ, G (x.1 + c, x.2) = G x) (z : ℝ × ℝ) :
    fderiv ℝ G (z.1 + c, z.2) = fderiv ℝ G z := by
  have hfun : (fun x : ℝ × ℝ => G (x + ((c:ℝ), (0:ℝ)))) = G := by
    funext x
    rw [show x + ((c:ℝ), (0:ℝ)) = (x.1 + c, x.2) by ext <;> simp]
    exact hG x
  have hsh : z + ((c:ℝ), (0:ℝ)) = (z.1 + c, z.2) := by ext <;> simp
  have h1 := fderiv_comp_add_right (𝕜 := ℝ) (f := G) (x := z) ((c:ℝ), (0:ℝ))
  rw [hfun, hsh] at h1
  exact h1.symm

/-- The slab divergence of a smooth force is continuous in the cell variables. -/
theorem swk_slab_cont (F : Profile → MeridC) (hF : ContDiff ℝ ∞ F) (σ : ℝ) :
    Continuous (fun y : ℝ × ℝ => slabDiv F σ y) := by
  have hcd : ∀ j : Fin 2, ContDiff ℝ ∞ (fun z : ℝ × ℝ => F (σ, z) j) := fun j =>
    (contDiff_comp_apply F hF j).comp (contDiff_const.prodMk contDiff_id)
  unfold slabDiv
  exact continuous_finsetSum _ (fun j _ =>
    ((hcd j).continuous_fderiv (by simp)).clm_apply continuous_const)

/-- **(W)** If the smooth force `F` satisfies the weak equation `∫ ⟪cgrad 0 Φ, F⟫ dμ_H = 0` for all
profile tests `Φ`, then every slice `F(σ,·)` is classically divergence free. -/
theorem slabWeakToClassical : UnforcedLeray.Short.PartIIa.N01.SlabWeakToClassical := by
  intro c hc F hF hwk σ y
  obtain ⟨hsmooth, hper, s₁, s₂, R, hs₁, hzero⟩ := hF
  rcases le_or_gt σ 0 with hσ | hσ
  · have hz : ∀ z : ℝ × ℝ, F (σ, z) = 0 := fun z => hzero (σ, z) (Or.inl (by simp; linarith))
    unfold slabDiv
    simp [hz]
  · -- the box statement from the weak equation and the periodic bump
    have hG : ∀ G : Profile → ℝ, ContDiff ℝ ∞ G → HasCompactSupport G →
        tsupport G ⊆ (Set.Ioi (0:ℝ) ×ˢ (Set.Ioo (0:ℝ) c ×ˢ (Set.univ : Set ℝ))) →
        ∫ p in (Set.Ioi (0:ℝ) ×ˢ (Set.Ioo (0:ℝ) c ×ˢ (Set.univ : Set ℝ))),
          (((p.1 ^ (-(3/2:ℝ)) : ℝ) : ℂ) * (((UnforcedLeray.Axi.dQ G p : ℝ) : ℂ) * F p 0 +
            ((UnforcedLeray.Axi.dEta G p : ℝ) : ℂ) * F p 1)) = 0 := by
      intro G hGs hGc hGsub
      obtain ⟨Φ, hΦ⟩ := periodicBumpTest c hc G hGs hGc hGsub
      have h1 := hwk Φ
      rw [swk_measureH_eq c Φ.1 F, setIntegral_congr_set (swk_cell_ae_box c)] at h1
      have hEq : (∫ p in (Set.Ioi (0:ℝ) ×ˢ (Set.Ioo (0:ℝ) c ×ˢ (Set.univ : Set ℝ))),
          (((p.1 ^ (-(3/2:ℝ)) : ℝ) : ℂ) * (((UnforcedLeray.Axi.dQ G p : ℝ) : ℂ) * F p 0 +
            ((UnforcedLeray.Axi.dEta G p : ℝ) : ℂ) * F p 1))) =
          ∫ p in (Set.Ioi (0:ℝ) ×ˢ (Set.Ioo (0:ℝ) c ×ˢ (Set.univ : Set ℝ))),
          (((p.1 ^ (-(3/2:ℝ)) : ℝ) : ℂ) * (((UnforcedLeray.Axi.dQ Φ.1 p : ℝ) : ℂ) * F p 0 +
            ((UnforcedLeray.Axi.dEta Φ.1 p : ℝ) : ℂ) * F p 1)) := by
        refine setIntegral_congr_fun (isOpen_cellBox c).measurableSet ?_
        intro p hp
        have hev : Φ.1 =ᶠ[nhds p] G :=
          Filter.eventually_of_mem ((isOpen_cellBox c).mem_nhds hp) (fun x hx => hΦ x hx)
        simp only [UnforcedLeray.Axi.dQ, UnforcedLeray.Axi.dEta]
        rw [hev.fderiv_eq]
      rw [hEq]
      exact h1
    have hslab := slabDivFundamental c hc F hsmooth hG
    -- the slice vanishes on the open cell `0 < q < c`, for `σ > 0`
    have hcl : IsClosed {y : ℝ × ℝ | slabDiv F σ y = 0} :=
      isClosed_eq (swk_slab_cont F hsmooth σ) continuous_const
    have hsub : Ioo (0:ℝ) c ×ˢ (univ : Set ℝ) ⊆ {y : ℝ × ℝ | slabDiv F σ y = 0} := by
      rintro ⟨q, η⟩ ⟨hq, -⟩
      exact hslab σ q η hσ hq.1 hq.2
    have hc2 : closure (Ioo (0:ℝ) c ×ˢ (univ : Set ℝ)) = Icc (0:ℝ) c ×ˢ (univ : Set ℝ) := by
      rw [closure_prod_eq, closure_Ioo hc.ne, closure_univ]
    have hcl' : Icc (0:ℝ) c ×ˢ (univ : Set ℝ) ⊆ {y : ℝ × ℝ | slabDiv F σ y = 0} := by
      rw [← hc2]
      exact closure_minimal hsub hcl
    -- periodicity in q
    have hper' : ∀ x : ℝ × ℝ, F (σ, (x.1 + c, x.2)) = F (σ, x) := fun x => hper (σ, x)
    have hperiod : ∀ (q η : ℝ), slabDiv F σ (q + c, η) = slabDiv F σ (q, η) := by
      intro q η
      unfold slabDiv
      refine Finset.sum_congr rfl (fun j _ => ?_)
      have e := swk_fderiv_shift c (fun w : ℝ × ℝ => F (σ, w) j)
        (fun x => by dsimp only; rw [hper' x]) (q, η)
      dsimp only at e
      rw [e]
    -- reduce `q` modulo `c` into `[0, c]`, using the closed set and periodicity
    have hfin : ∀ (η q : ℝ), slabDiv F σ (q, η) = 0 := by
      intro η q
      have hPer : Function.Periodic (fun x : ℝ => slabDiv F σ (x, η)) c :=
        fun x => hperiod x η
      have hA : (⌊q / c⌋ : ℝ) * c ≤ q := (le_div_iff₀ hc).mp (Int.floor_le _)
      have hB : q < ((⌊q / c⌋ : ℝ) + 1) * c := (div_lt_iff₀ hc).mp (Int.lt_floor_add_one _)
      have hB' : ((⌊q / c⌋ : ℝ) + 1) * c = (⌊q / c⌋ : ℝ) * c + c := by ring
      have h0 : 0 ≤ q - (⌊q / c⌋ : ℝ) * c := by linarith
      have h1 : q - (⌊q / c⌋ : ℝ) * c ≤ c := by linarith
      have hpk : slabDiv F σ (q - (⌊q / c⌋ : ℝ) * c, η) = slabDiv F σ (q, η) :=
        hPer.sub_int_mul_eq ⌊q / c⌋
      rw [← hpk]
      exact hcl' ⟨⟨h0, h1⟩, trivial⟩
    obtain ⟨q, η⟩ := y
    exact hfin η q
end UnforcedLeray.Short.PartIIa.N01
