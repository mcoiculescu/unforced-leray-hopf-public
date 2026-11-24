import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_3_1_1_org.Leaf2Duality.FreeAdjExists.HkStep
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.End.Leaf.SmoothAeJet
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T22_2_3_1_7

/-!
# Regular free adjoint flow from spatial smoothness and pointwise PDE

Source of record: `the November 2 reference manuscript` (SP), lines 2937-2958,
3036-3037, and 3060-3073.

Combines:
* `freeAdjointFlow_of_smooth`: upgrades `IsFreeAdjointWeak`, `AdjHkOn c m 1 (Ico t s) φ`, and a
  jointly smooth version on `[t, s) × ℝ²` to `IsFreeAdjointFlow` (via `smoothAeJet`);
* `freeJointSmooth_of_spPde`: upgrades a spatially smooth version solving the backward free PDE
  pointwise on `[t, b]` (`b < s`) to joint `C^∞` regularity on `[t, s) × ℝ²` for all `0 < ν` via
  `BwdRoute.fwdJointSmooth_proved` applied to real and imaginary parts;
* `freeAdjExists_of_spPde`: reduces `Leaf2DualityNeeded.FreeAdjExists` for all `0 < ν` (`8 < m`)
  to the two focused leaves `FreeSpSmoothRep` and `FreePointwisePde`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa.ComplFreeRateSub

/-- Commutation of a continuous `ℝ`-linear functional `L : ℂ →L[ℝ] ℝ` with `B0579.pd`/`pdCx`. -/
theorem pd_comp_clm (L : ℂ →L[ℝ] ℝ) {g : ℝ × ℝ → ℂ} (hg : Differentiable ℝ g) (j : Fin 2) :
    B0579.pd j (fun y => L (g y)) = fun y => L (pdCx j g y) := by
  funext y
  unfold B0579.pd pdCx
  change fderiv ℝ (L ∘ g) y (B0579.dir j) = L (fderiv ℝ g y (B0579.dir j))
  rw [(L.hasFDerivAt.comp y (hg y).hasFDerivAt).fderiv]
  rfl

/-- Commutation of `L : ℂ →L[ℝ] ℝ` with iterated spatial partials `pdW` / `adjSpatial`. -/
theorem pdW_comp_clm (L : ℂ →L[ℝ] ℝ) (w : List (Fin 2)) {g : ℝ × ℝ → ℂ} (hg : ContDiff ℝ ∞ g) :
    UnforcedLeray.Short.IIb.BwdRoute.pdW w (fun y => L (g y)) =
      fun y => L (adjSpatial w g y) := by
  induction w with
  | nil => rfl
  | cons j w ih =>
    simp only [UnforcedLeray.Short.IIb.BwdRoute.pdW, adjSpatial, ih]
    exact pd_comp_clm L ((contDiff_adjSpatial hg w).differentiable (by simp)) j

/-- Commutation of `L : ℂ →L[ℝ] ℝ` with the planar Laplacian `IIb.lapP` / `stLap`. -/
theorem lapP_comp_clm (L : ℂ →L[ℝ] ℝ) {g : ℝ × ℝ → ℂ} (hg : ContDiff ℝ ∞ g) (x : ℝ × ℝ) :
    UnforcedLeray.Short.IIb.lapP (fun y => L (g y)) x = L (stLap g x) := by
  have h0 := congrFun (pdW_comp_clm L [0, 0] hg) x
  have h1 := congrFun (pdW_comp_clm L [1, 1] hg) x
  simp only [UnforcedLeray.Short.IIb.BwdRoute.pdW] at h0 h1
  unfold UnforcedLeray.Short.IIb.lapP stLap
  rw [h0, h1, map_add]

/-- Joint `C^∞` regularity on `[t, s) × ℝ²` from spatial smoothness, joint continuity of spatial
partials, and the pointwise backward PDE on `[t, b]` (`b < s`), valid for every `ν` (`0 ≤ t < s`)
via `BwdRoute.fwdJointSmooth_proved`. -/
theorem freeJointSmooth_of_spPde {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c)
    {t s : ℝ} (ht : 0 ≤ t) {φ' : ℝ → ℝ × ℝ → ℂ}
    (hsm : ∀ r ∈ Ico t s, ContDiff ℝ ∞ (φ' r))
    (hcont : ∀ w : List (Fin 2),
      ContinuousOn (fun p : ℝ × (ℝ × ℝ) => adjSpatial w (φ' p.1) p.2) (Ico t s ×ˢ univ))
    (hpde : ∀ b ∈ Ioo t s, ∀ r ∈ Icc t b, ∀ x : ℝ × ℝ,
      HasDerivWithinAt (fun r' => φ' r' x)
        (-((ν : ℂ) * stLap (φ' r) x +
          (((tr.v r x 0 : ℝ) : ℂ) * pdCx 0 (φ' r) x +
            ((tr.v r x 1 : ℝ) : ℂ) * pdCx 1 (φ' r) x)))
        (Icc t b) r) :
    ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => φ' p.1 p.2) (Ico t s ×ˢ univ) := by
  have hb_all : ∀ b ∈ Ioo t s,
      ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => φ' p.1 p.2) (Icc t b ×ˢ univ) := by
    intro b hb
    set T : ℝ := b - t with hT_def
    have hT : 0 < T := sub_pos.2 hb.1
    set w := UnforcedLeray.Short.IIb.BwdRoute.revDrift b tr.v with hw_def
    have hws := UnforcedLeray.Short.IIb.BwdRoute.revDrift_smooth tr (s := t) (t := b) ht
    have hmemIcc : ∀ σ ∈ Icc (0 : ℝ) T, b - σ ∈ Icc t b := fun σ hσ =>
      ⟨by linarith [hσ.2], by linarith [hσ.1]⟩
    have hmemIco : ∀ σ ∈ Icc (0 : ℝ) T, b - σ ∈ Ico t s := fun σ hσ =>
      ⟨(hmemIcc σ hσ).1, (hmemIcc σ hσ).2.trans_lt hb.2⟩
    have hpart : ∀ L : ℂ →L[ℝ] ℝ, (∀ z : ℂ, ∀ a : ℝ, L ((a : ℂ) * z) = a * L z) →
        ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => L (φ' p.1 p.2)) (Icc t b ×ˢ univ) := by
      intro L hLmul
      let u : ℝ → UnforcedLeray.Short.IIb.CylPDE.Pl → ℝ := fun σ x => L (φ' (b - σ) x)
      have hsp : UnforcedLeray.Short.IIb.BwdRoute.SpSmooth T u := by
        refine ⟨fun σ hσ => L.contDiff.comp (hsm (b - σ) (hmemIco σ hσ)), fun l => ?_⟩
        have hmaps : MapsTo (fun z : ℝ × (ℝ × ℝ) => (b - z.1, z.2))
            (Icc 0 T ×ˢ univ) (Ico t s ×ˢ univ) :=
          fun z hz => ⟨hmemIco z.1 hz.1, mem_univ _⟩
        have hc1 : ContinuousOn (fun z : ℝ × (ℝ × ℝ) => L (adjSpatial l (φ' (b - z.1)) z.2))
            (Icc 0 T ×ˢ univ) :=
          L.continuous.comp_continuousOn
            ((hcont l).comp ((continuous_const.sub continuous_fst).prodMk continuous_snd).continuousOn
              hmaps)
        refine hc1.congr fun z hz => ?_
        exact congrFun (pdW_comp_clm L l (hsm (b - z.1) (hmemIco z.1 hz.1))) z.2
      have hfpde : UnforcedLeray.Short.IIb.BwdRoute.FwdPde ν T w u := by
        intro σ hσ x
        have hrI : b - σ ∈ Icc t b := hmemIcc σ hσ
        have hrC : b - σ ∈ Ico t s := hmemIco σ hσ
        have hrev : HasDerivWithinAt (fun τ : ℝ => b - τ) (-1) (Icc 0 T) σ :=
          (hasDerivWithinAt_id σ (Icc 0 T)).const_sub b
        have hd1 := HasDerivWithinAt.scomp (𝕜 := ℝ) σ (hpde b hb (b - σ) hrI x) hrev
          (fun τ hτ => hmemIcc τ hτ)
        have hd2 : HasDerivWithinAt (fun τ => u τ x)
            (L ((-1 : ℝ) • -((ν : ℂ) * stLap (φ' (b - σ)) x +
              (((tr.v (b - σ) x 0 : ℝ) : ℂ) * pdCx 0 (φ' (b - σ)) x +
                ((tr.v (b - σ) x 1 : ℝ) : ℂ) * pdCx 1 (φ' (b - σ)) x))))
            (Icc 0 T) σ := by
          have := L.hasFDerivAt.comp_hasDerivWithinAt σ hd1
          simpa [Function.comp_def] using this
        refine hd2.congr_deriv ?_
        have hlap := lapP_comp_clm L (hsm (b - σ) hrC) x
        have hpd0 := congrFun (pd_comp_clm L ((hsm (b - σ) hrC).differentiable (by simp)) 0) x
        have hpd1 := congrFun (pd_comp_clm L ((hsm (b - σ) hrC).differentiable (by simp)) 1) x
        have hw0 : w σ x 0 = -tr.v (b - σ) x 0 := by simp [hw_def, UnforcedLeray.Short.IIb.BwdRoute.revDrift]
        have hw1 : w σ x 1 = -tr.v (b - σ) x 1 := by simp [hw_def, UnforcedLeray.Short.IIb.BwdRoute.revDrift]
        rw [neg_one_smul, neg_neg, map_add, map_add, hLmul, hLmul, hLmul]
        change ν * L (stLap (φ' (b - σ)) x) +
            (tr.v (b - σ) x 0 * L (pdCx 0 (φ' (b - σ)) x) +
              tr.v (b - σ) x 1 * L (pdCx 1 (φ' (b - σ)) x)) =
          ν * UnforcedLeray.Short.IIb.lapP (fun y => L (φ' (b - σ) y)) x -
            (w σ x 0 * B0579.pd 0 (fun y => L (φ' (b - σ) y)) x +
              w σ x 1 * B0579.pd 1 (fun y => L (φ' (b - σ) y)) x)
        rw [hlap, hpd0, hpd1, hw0, hw1]
        ring
      have husm := UnforcedLeray.Short.IIb.BwdRoute.fwdJointSmooth_proved ν T w u hT.le hws hsp hfpde
      have hmaps : MapsTo (fun p : ℝ × (ℝ × ℝ) => (b - p.1, p.2))
          (Icc t b ×ˢ univ) (Icc 0 T ×ˢ univ) :=
        fun p hp => ⟨⟨by linarith [hp.1.2], by linarith [hp.1.1]⟩, mem_univ _⟩
      have hcomp := husm.comp (UnforcedLeray.Short.IIb.BwdRoute.contDiff_rev b).contDiffOn hmaps
      refine hcomp.congr fun p _ => ?_
      change L (φ' p.1 p.2) = L (φ' (b - (b - p.1)) p.2)
      rw [sub_sub_cancel]
    have hre := hpart Complex.reCLM (fun z a => by simp)
    have him := hpart Complex.imCLM (fun z a => by simp)
    have hsum : ContDiffOn ℝ ∞
        (fun p : ℝ × (ℝ × ℝ) => (Complex.ofRealCLM (Complex.reCLM (φ' p.1 p.2))) +
          Complex.I * (Complex.ofRealCLM (Complex.imCLM (φ' p.1 p.2))))
        (Icc t b ×ˢ univ) :=
      (Complex.ofRealCLM.contDiff.comp_contDiffOn hre).add
        (contDiffOn_const.mul (Complex.ofRealCLM.contDiff.comp_contDiffOn him))
    refine hsum.congr fun p _ => ?_
    simp only [Complex.ofRealCLM_apply, Complex.reCLM_apply, Complex.imCLM_apply]
    exact (Complex.re_add_im (φ' p.1 p.2)).symm.trans (by ring)
  intro p hp
  set b : ℝ := (p.1 + s) / 2
  have hpb : p.1 < b := by simp only [b]; linarith [hp.1.2]
  have hbs : b < s := by simp only [b]; linarith [hp.1.2]
  have hbI : b ∈ Ioo t s := ⟨hp.1.1.trans_lt hpb, hbs⟩
  have hpB : p ∈ Icc t b ×ˢ (univ : Set (ℝ × ℝ)) := ⟨⟨hp.1.1, hpb.le⟩, mem_univ _⟩
  refine (hb_all b hbI p hpB).mono_of_mem_nhdsWithin ?_
  have hopen : Iio b ×ˢ (univ : Set (ℝ × ℝ)) ∈ 𝓝 p :=
    (isOpen_Iio.prod isOpen_univ).mem_nhds ⟨hpb, mem_univ _⟩
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds hopen] with q hq1 hq2
  exact ⟨⟨hq1.1.1, hq2.1.le⟩, mem_univ _⟩

/-- Upgrade `IsFreeAdjointWeak` + `AdjHkOn c m 1 (Ico t s) φ` + a jointly `C^∞` version on
`[t, s) × ℝ²` to a full `IsFreeAdjointFlow`. -/
theorem freeAdjointFlow_of_smooth {ν c m t s : ℝ} (hc : 0 < c) (hts : t < s)
    {tr : UnforcedLeray.B0140.TrainSol ν c} {g : ℝ × ℝ → ℂ} {φ ψ : ℝ → ℝ × ℝ → ℂ}
    (hφ : IsFreeAdjointWeak ν c m tr t s g φ)
    (hH1 : AdjHkOn c m 1 (Ico t s) φ)
    (hψae : ∀ r ∈ Ico t s, ψ r =ᵐ[volume] φ r)
    (hψj : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => ψ p.1 p.2) (Ico t s ×ˢ univ)) :
    ∃ φ' : ℝ → ℝ × ℝ → ℂ, IsFreeAdjointFlow ν c m tr t s g φ' := by
  let φ' : ℝ → ℝ × ℝ → ℂ := fun r => if r < s then ψ r else φ r
  have hEq : ∀ r ∈ Ico t s, φ' r = ψ r := fun r hr => by simp only [φ', hr.2, ↓reduceIte]
  have hj' : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => φ' p.1 p.2) (Ico t s ×ˢ univ) :=
    hψj.congr fun p hp => by rw [hEq p.1 hp.1]
  have hsm : ∀ r ∈ Ico t s, ContDiff ℝ ∞ (φ' r) := fun r hr => adjContDiff_slice hj' hr
  have hae : ∀ r ∈ Icc t s, φ' r =ᵐ[volume] φ r := by
    intro r hr
    by_cases hrs : r < s
    · rw [hEq r ⟨hr.1, hrs⟩]
      exact hψae r ⟨hr.1, hrs⟩
    · simp only [φ', hrs, ↓reduceIte]
      exact EventuallyEq.rfl
  have hper : ∀ r ∈ Ico t s, ∀ x : ℝ × ℝ, φ' r (x.1 + c, x.2) = φ' r x :=
    fun r hr => adjPeriodic_of_ae_eq (hsm r hr).continuous (hae r (Ico_subset_Icc_self hr))
      (hφ.periodic r hr)
  have hw : IsFreeAdjointWeak ν c m tr t s g φ' := hφ.congr_ae hts.le hae hper
  obtain ⟨D, hDj, hDc⟩ := hH1
  have hac : B0579.cellMeasure c (-m) ≪ volume :=
    (B0579.cellMeasure_ac c (-m)).trans Measure.restrict_le_self.absolutelyContinuous
  have haeDX : ∀ r ∈ Ico t s, ∀ k : Fin 2,
      pdCx k (φ' r) =ᵐ[B0579.cellMeasure c (-m)] D r [k] := by
    intro r hr k
    exact hac.ae_eq ((smoothAeJet c m 1 (φ' r) (φ r) (D r) hc (hsm r hr) (hDj r hr)
      (hae r (Ico_subset_Icc_self hr)) [k] (by simp)).2)
  refine ⟨φ', {
    terminal := hw.terminal
    memX := hw.memX
    strongCont := hw.strongCont
    periodic := hper
    smooth := hsm
    jointSmooth := hj'
    memH1 := fun r hr k => ((hDj r hr).memX [k] (by simp)).ae_eq (haeDX r hr k).symm
    strongContH1 := fun r hr k => by
      refine (hDc [k] (by simp) r hr).congr' ?_
      filter_upwards [self_mem_nhdsWithin] with r' hr'
      unfold xNorm
      exact eLpNorm_congr_ae ((haeDX r' hr' k).symm.sub (haeDX r hr k).symm)
    integrable := hw.integrable
    timeIntegrable := hw.timeIntegrable
    weak := hw.weak }⟩

namespace Leaf2DualityNeeded

/-- **Leaf 1 (`FreeSpSmoothRep`)** (SP 3060-3061): any family `φ` lying in `C([t, s); H^k_{-m,c})`
for all `k : ℕ` (`AdjHkOn`) admits a `c`-periodic spatially `C^∞` representative `φ'` on `[t, s)`
whose iterated spatial partials `adjSpatial w (φ' r)` are jointly continuous on `[t, s) × ℝ²`
(take `φ' r x = lim_{n → ∞} cellMoll n (φ r) x`, which converges locally uniformly along with all
spatial derivatives by `cellMollTendsto`, `adjSpatial_cellMoll_jet`, and `supBddByXNorm`). -/
def FreeSpSmoothRep (c m t s : ℝ) : Prop :=
  0 < c → t < s → ∀ φ : ℝ → ℝ × ℝ → ℂ, (∀ k : ℕ, AdjHkOn c m k (Ico t s) φ) →
    ∃ φ' : ℝ → ℝ × ℝ → ℂ,
      (∀ r ∈ Ico t s, φ' r =ᵐ[volume] φ r) ∧
      (∀ r ∈ Ico t s, ContDiff ℝ ∞ (φ' r)) ∧
      (∀ r ∈ Ico t s, ∀ x : ℝ × ℝ, φ' r (x.1 + c, x.2) = φ' r x) ∧
      ∀ w : List (Fin 2),
        ContinuousOn (fun p : ℝ × (ℝ × ℝ) => adjSpatial w (φ' p.1) p.2) (Ico t s ×ˢ univ)

/-- **Leaf 2 (`FreePointwisePde`)** (SP 2937-2958, 3060): a spatially smooth `c`-periodic
representative `φ'` of `IsFreeAdjointWeak` with jointly continuous spatial partials satisfies the
backward free PDE `-∂_r φ' = ν Δ φ' + v · ∇ φ'` pointwise within `[t, b]` for every `b ∈ (t, s)`
(integrate `freeAdjIntegrand` by parts via `cellIBP`, so `FreeTestedDeriv` equates the cell pairing
of the continuous `c`-periodic difference against every cylinder test `ψ` to `0`, then test against
periodized `molKer n (x - ·)` or apply `weakCellAeUnique` / continuity). -/
def FreePointwisePde (ν m : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)))
    (t s : ℝ) : Prop :=
  0 < ν → 0 ≤ t → t < s →
    ∀ (g : ℝ × ℝ → ℂ) (φ φ' : ℝ → ℝ × ℝ → ℂ),
      IsFreeAdjointWeak ν (ν ^ (-2 : ℝ)) m tr t s g φ →
      FreeTestedDeriv tr t s φ →
      (∀ r ∈ Ico t s, φ' r =ᵐ[volume] φ r) →
      (∀ r ∈ Ico t s, ContDiff ℝ ∞ (φ' r)) →
      (∀ r ∈ Ico t s, ∀ x : ℝ × ℝ, φ' r (x.1 + ν ^ (-2 : ℝ), x.2) = φ' r x) →
      (∀ w : List (Fin 2),
        ContinuousOn (fun p : ℝ × (ℝ × ℝ) => adjSpatial w (φ' p.1) p.2) (Ico t s ×ˢ univ)) →
      ∀ b ∈ Ioo t s, ∀ r ∈ Icc t b, ∀ x : ℝ × ℝ,
        HasDerivWithinAt (fun r' => φ' r' x)
          (-((ν : ℂ) * stLap (φ' r) x +
            (((tr.v r x 0 : ℝ) : ℂ) * pdCx 0 (φ' r) x +
              ((tr.v r x 1 : ℝ) : ℂ) * pdCx 1 (φ' r) x)))
          (Icc t b) r

/-- **Assembly of `FreeAdjExists`** for all `0 < ν` and `8 < m` from `FreeSpSmoothRep` and
`FreePointwisePde` (combining `freeAdjWeak_exists`, `freeAdjExists_eq`, `freeTestedDeriv`,
`freeHkAllOrders`, `freeJointSmooth_of_spPde`, and `freeAdjointFlow_of_smooth`). -/
theorem freeAdjExists_of_spPde (ν m : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)))
    (t₁ t₂ : ℝ)
    (hSp : ∀ s ∈ Ioc t₁ t₂, FreeSpSmoothRep (ν ^ (-2 : ℝ)) m t₁ s)
    (hPde : ∀ s ∈ Ioc t₁ t₂, FreePointwisePde ν m tr t₁ s) :
    FreeAdjExists ν m tr t₁ t₂ := by
  intro hm hν ht₁ _ hbuc s hs Γ hΓ
  let c : ℝ := ν ^ (-2 : ℝ)
  have hc : 0 < c := Real.rpow_pos_of_pos hν _
  have hs0 : 0 ≤ s := ht₁.trans hs.1
  have ha : 1 ≤ clockA ν s := by
    unfold clockA
    nlinarith [mul_nonneg hν.le hs0]
  have hgm : MemLp (physAdj (clockA ν s) Γ) 2 (B0579.cellMeasure c (-m)) :=
    adjTerminalMem m (by linarith) c (clockA ν s) hc ha Γ hΓ
  rcases eq_or_lt_of_le hs.1 with rfl | hlt
  · exact freeAdjExists_eq hν tr hbuc ht₁ hgm
  · obtain ⟨φ, hφ⟩ := freeAdjWeak_exists hm hν tr hbuc ht₁ hlt hgm
    have hTD := freeTestedDeriv tr hbuc ht₁ hlt hφ
    have hHk := freeHkAllOrders hν tr hbuc ht₁ hlt hφ hTD
    obtain ⟨φ', hφ'ae, hφ'sm, hφ'per, hφ'cont⟩ := hSp s ⟨hlt, hs.2⟩ hc hlt φ hHk
    have hpde := hPde s ⟨hlt, hs.2⟩ hν ht₁ hlt _ φ φ' hφ hTD hφ'ae hφ'sm hφ'per hφ'cont
    have hj := freeJointSmooth_of_spPde tr ht₁ hφ'sm hφ'cont hpde
    exact freeAdjointFlow_of_smooth hc hlt hφ (hHk 1) hφ'ae hj

end Leaf2DualityNeeded

end UnforcedLeray.Short.IIIa.ComplFreeRateSub
