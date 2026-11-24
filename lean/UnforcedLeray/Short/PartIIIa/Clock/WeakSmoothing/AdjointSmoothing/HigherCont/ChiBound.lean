import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_7_2_4
import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.HkStep.KT.Of
import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.HkStep.KT.CommuteOf
import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.HkStep.Energy.Defs
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_1.KernelAdjoint
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.HkStep.KT.KTSource
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.HkStep.KT.KTPairInt
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.HkStep.KT.KTWeakMeas
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.HkStep.KT.KTWeakCong
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.HkStep.KT.KTWeakAdd
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.HkStep.KT.KTCoeffDeriv
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.HkStep.KT.KTTestInt
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.HkStep.KT.KerVelSmooth
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.HkStep.KT.KTWeakLeibniz
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.HkStep.KT.KTWeakIBP
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.HkStep.KT.KerVelIsBS
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.AdjWeakChi.Identify
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.End.Leaf.SmoothAeJet
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.LadDtRegular

/-!
# `PartIII-a:T21/2/7/2/4/1`: weighted `X_{-m,c}` bound on `∂^w χ` from the train jets

Source of record: `the November 2 reference manuscript`
(SP), lines 3052-3058, 3060-3073.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff Interval

namespace UnforcedLeray.Short.IIIa

namespace ChiBoundAux

lemma xNorm_le_h1Norm_both (c m : ℝ) (φ : ℝ × ℝ → ℂ) (g : Fin 2 → ℝ × ℝ → ℂ) :
    xNorm c (-m) φ ≤ h1Norm c m φ g ∧ ∀ j, xNorm c (-m) (g j) ≤ h1Norm c m φ g := by
  have key : ∀ a : ℝ≥0∞, a ^ 2 ≤ xNorm c (-m) φ ^ 2 + ∑ j, xNorm c (-m) (g j) ^ 2 →
      a ≤ h1Norm c m φ g := by
    intro a ha
    unfold h1Norm
    calc a = (a ^ 2) ^ (1 / 2 : ℝ) := by
          rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num
      _ ≤ _ := ENNReal.rpow_le_rpow ha (by norm_num)
  refine ⟨key _ le_self_add, fun j => key _ ?_⟩
  refine le_trans ?_ le_add_self
  exact Finset.single_le_sum (f := fun j => xNorm c (-m) (g j) ^ 2) (fun _ _ => zero_le)
    (Finset.mem_univ j)

def ktJet1 (χ : ℝ × ℝ → ℂ) (g : Fin 2 → ℝ × ℝ → ℂ) : List (Fin 2) → ℝ × ℝ → ℂ
  | [] => χ
  | [k] => g k
  | _ :: _ :: _ => 0

def KTAtU (m c : ℝ) (j : ℕ) : Prop :=
  ∀ (A : ℝ), ∃ C : ℝ, 0 ≤ C ∧ ∀ (B : Fin 2 → ℝ × ℝ → ℝ),
    (∀ l, ContDiff ℝ ∞ (B l)) → (∀ l (x : ℝ × ℝ), B l (x.1 + c, x.2) = B l x) →
    KTCoeffBound m j B A →
    ∀ (f : ℝ × ℝ → ℂ) (D : List (Fin 2) → ℝ × ℝ → ℂ), IsCellJet c m j f D →
      ∃ (χ : ℝ × ℝ → ℂ) (Dχ : List (Fin 2) → ℝ × ℝ → ℂ), IsCellJet c m (j + 1) χ Dχ ∧
        (∀ w : List (Fin 2), w.length ≤ j + 1 →
          xNorm c (-m) (Dχ w) ≤ ENNReal.ofReal C * jetNorm c m j D) ∧
        KTPairing c f B χ

def KTBaseU (m : ℝ) : Prop := 1 < m → ∀ c : ℝ, 1 ≤ c → KTAtU m c 0

theorem ktAtU_succ {m c : ℝ} (hm : 1 < m) (hc : 1 ≤ c) (hBase : KTBaseU m) (hComm : KTCommute m)
    (hCD : KTCoeffDeriv) (hAdd : KTWeakAdd) (j : ℕ) (ih : KTAtU m c j) : KTAtU m c (j + 1) := by
  intro A
  obtain ⟨C0, hC0, H0⟩ := hBase hm c hc A
  obtain ⟨C1, hC1, H1⟩ := ih A
  refine ⟨C0 + C1 + C1 + C1, by linarith, ?_⟩
  intro B hBs hBp hBb
  have hb1 : KTCoeffBound m 1 B A := fun l i hi x => hBb l i (by omega) x
  have hb0 : KTCoeffBound m 0 B A := fun l i hi x => hBb l i (by omega) x
  have hbj : KTCoeffBound m j B A := fun l i hi x => hBb l i (hi.trans (Nat.le_succ _)) x
  have hder := fun k : Fin 2 => hCD m c j B A k hBs hBp hBb
  have H2 := fun k : Fin 2 => H1 (fun l => B0579.pd k (B l)) (hder k).1 (hder k).2.1 (hder k).2.2
  have H0 := H0 B hBs hBp hb0
  have H1 := H1 B hBs hBp hbj
  intro f D hJ
  obtain ⟨χ, Dχ, hχJ, hχN, hχP⟩ := H0 f D (hJ.mono (Nat.zero_le _))
  have hex : ∀ k : Fin 2, ∃ (χ₁ χ₂ : ℝ × ℝ → ℂ) (E₁ E₂ : List (Fin 2) → ℝ × ℝ → ℂ),
      IsCellJet c m (j + 1) χ₁ E₁ ∧ IsCellJet c m (j + 1) χ₂ E₂ ∧
      (∀ w : List (Fin 2), w.length ≤ j + 1 →
        xNorm c (-m) (E₁ w) ≤ ENNReal.ofReal C1 * jetNorm c m j (fun w => D (w ++ [k]))) ∧
      (∀ w : List (Fin 2), w.length ≤ j + 1 →
        xNorm c (-m) (E₂ w) ≤ ENNReal.ofReal C1 * jetNorm c m j D) ∧
      KTPairing c (D [k]) B χ₁ ∧ KTPairing c f (fun l => B0579.pd k (B l)) χ₂ := by
    intro k
    obtain ⟨χ₁, E₁, a1, a2, a3⟩ := H1 (D [k]) (fun w => D (w ++ [k])) (hJ.shift k)
    obtain ⟨χ₂, E₂, b1, b2, b3⟩ := H2 k f D (hJ.mono (Nat.le_succ _))
    exact ⟨χ₁, χ₂, E₁, E₂, a1, b1, a2, b2, a3, b3⟩
  choose χ₁ χ₂ E₁ E₂ hE₁ hE₂ hN₁ hN₂ hP₁ hP₂ using hex
  have hcomm : ∀ k : Fin 2, HasWeakCellDerivC c k χ (χ₁ k + χ₂ k) := by
    intro k
    have hχ0 : MemLp χ 2 (B0579.cellMeasure c (-m)) := by
      have := hχJ.memX [] (Nat.zero_le _)
      rwa [hχJ.base] at this
    have hf0 : MemLp f 2 (B0579.cellMeasure c (-m)) := by
      have := hJ.memX [] (Nat.zero_le _)
      rwa [hJ.base] at this
    exact hComm hm c hc B A k hBs hBp hb1 f (D [k]) χ (χ₁ k) (χ₂ k) hf0
      (by simpa using hJ.memX [k] (by simp)) hχ0
      (by simpa [(hE₁ k).base] using (hE₁ k).memX [] (Nat.zero_le _))
      (by simpa [(hE₂ k).base] using (hE₂ k).memX [] (Nat.zero_le _))
      (by simpa [hJ.base] using hJ.deriv k [] (Nat.succ_pos _)) hχP (hP₁ k) (hP₂ k)
  refine ⟨χ, ktGlue χ (fun k => E₁ k + E₂ k), ?_, ?_, hχP⟩
  · have hJk : ∀ k : Fin 2, IsCellJet c m (j + 1) (χ₁ k + χ₂ k) (E₁ k + E₂ k) :=
      fun k => (hE₁ k).add hAdd (hE₂ k)
    have hbase : ∀ k : Fin 2, (E₁ k + E₂ k) [] = χ₁ k + χ₂ k := fun k => (hJk k).base
    have hχ0 : ktGlue χ (fun k => E₁ k + E₂ k) [] = χ := rfl
    refine ⟨hχ0, ?_, ?_, ?_⟩
    · intro w hw x
      rcases ktSplit w with rfl | ⟨L, k, rfl⟩
      · have := hχJ.periodic [] (Nat.zero_le _) x
        rwa [hχJ.base] at this
      · rw [ktGlue_append]
        exact (hJk k).periodic L (by simpa using hw) x
    · intro w hw
      rcases ktSplit w with rfl | ⟨L, k, rfl⟩
      · have := hχJ.memX [] (Nat.zero_le _)
        rwa [hχJ.base] at this
      · rw [ktGlue_append]
        exact (hJk k).memX L (by simpa using hw)
    · intro i w hw
      rcases ktSplit w with rfl | ⟨L, k, rfl⟩
      · have := hcomm i
        rw [show [i] = [] ++ [i] from rfl, ktGlue_append, ktGlue_nil]
        simpa [← hbase i] using this
      · rw [show i :: (L ++ [k]) = (i :: L) ++ [k] from rfl, ktGlue_append, ktGlue_append]
        exact (hJk k).deriv i L (by simpa using hw)
  · intro w hw
    rcases ktSplit w with rfl | ⟨w', k, rfl⟩
    · calc xNorm c (-m) (ktGlue χ (fun k => E₁ k + E₂ k) []) = xNorm c (-m) χ := rfl
        _ ≤ ENNReal.ofReal C0 * jetNorm c m 0 D := by
          have := hχN [] (Nat.zero_le _)
          rwa [hχJ.base] at this
        _ ≤ ENNReal.ofReal (C0 + C1 + C1 + C1) * jetNorm c m (j + 1) D := by
          refine mul_le_mul' ?_ (jetNorm_mono c m (Nat.zero_le _) D)
          exact ENNReal.ofReal_le_ofReal (by linarith [hC1, hC1])
    · rw [ktGlue_append]
      have hw' : w'.length ≤ j + 1 := by simpa using hw
      have e : xNorm c (-m) ((E₁ k + E₂ k) w') ≤
          xNorm c (-m) (E₁ k w') + xNorm c (-m) (E₂ k w') := by
        unfold xNorm
        exact eLpNorm_add_le ((hE₁ k).memX w' hw').aestronglyMeasurable
          ((hE₂ k).memX w' hw').aestronglyMeasurable (by norm_num)
      have j1 : jetNorm c m j (fun w => D (w ++ [k])) ≤ jetNorm c m (j + 1) D :=
        jetNorm_shift_le c m j k D
      have j2 : jetNorm c m j D ≤ jetNorm c m (j + 1) D := jetNorm_mono c m (Nat.le_succ _) D
      have hsum : ENNReal.ofReal C1 + ENNReal.ofReal C1 ≤
          ENNReal.ofReal (C0 + C1 + C1 + C1) := by
        rw [← ENNReal.ofReal_add hC1 hC1]
        exact ENNReal.ofReal_le_ofReal (by linarith [hC0, hC1])
      calc xNorm c (-m) ((E₁ k + E₂ k) w')
          ≤ xNorm c (-m) (E₁ k w') + xNorm c (-m) (E₂ k w') := e
        _ ≤ ENNReal.ofReal C1 * jetNorm c m j (fun w => D (w ++ [k])) +
            ENNReal.ofReal C1 * jetNorm c m j D :=
          add_le_add (hN₁ k w' hw') (hN₂ k w' hw')
        _ ≤ ENNReal.ofReal C1 * jetNorm c m (j + 1) D +
            ENNReal.ofReal C1 * jetNorm c m (j + 1) D :=
          add_le_add (mul_le_mul' le_rfl j1) (mul_le_mul' le_rfl j2)
        _ = (ENNReal.ofReal C1 + ENNReal.ofReal C1) * jetNorm c m (j + 1) D := by
          rw [add_mul]
        _ ≤ _ := mul_le_mul' hsum le_rfl

theorem ktBaseU_of (m : ℝ) (hK : KernelAdjointBound m) (hS : KTSource) (hP : KTPairInt)
    (hM : KTWeakMeas) (hCong : KTWeakCong) : KTBaseU m := by
  intro hm c hc A
  have hc0 : 0 < c := by linarith
  obtain ⟨CS, hCS, HS0⟩ := hS m hm c hc0 A
  obtain ⟨CK, hCK, HK⟩ := hK hm
  refine ⟨2 * CK * CS, by positivity, ?_⟩
  intro B hBs hBp hb
  have HS := HS0 B (fun l => (hBs l).continuous) (by
    intro l x
    have := hb l 0 le_rfl x
    simpa using this)
  intro f D hJ
  have hf0 : MemLp f 2 (B0579.cellMeasure c (-m)) := by
    have := hJ.memX [] (Nat.zero_le _)
    rwa [hJ.base] at this
  have hjet : jetNorm c m 0 D = xNorm c (-m) f := by
    simp [jetNorm, wordsLE, hJ.base]
  set F : Fin 2 → ℝ × ℝ → ℂ := fun l x => f x * (B l x : ℂ) with hF
  have hFs := fun l => HS f hf0 l
  obtain ⟨χ0, gχ, hweak, hnorm, hpair⟩ :=
    HK c hc F (fun l => ⟨(hFs l).1, (hFs l).2.1⟩)
  obtain ⟨hmeas0, hmeasg⟩ := hM c χ0 gχ hc0 hweak
  have hsumle : ∑ j, (eLpNorm (F j) 1 (volume.restrict (B0579.cell c)) +
      eLpNorm (F j) 2 (volume.restrict (B0579.cell c))) ≤
        2 * (ENNReal.ofReal CS * xNorm c (-m) f) := by
    rw [Fin.sum_univ_two, two_mul]
    exact add_le_add (hFs 0).2.2 (hFs 1).2.2
  have hH : h1Norm c m χ0 gχ ≤ ENNReal.ofReal (2 * CK * CS) * xNorm c (-m) f := by
    calc h1Norm c m χ0 gχ ≤ ENNReal.ofReal CK * ∑ j, (eLpNorm (F j) 1
          (volume.restrict (B0579.cell c)) + eLpNorm (F j) 2 (volume.restrict (B0579.cell c))) :=
          hnorm
      _ ≤ ENNReal.ofReal CK * (2 * (ENNReal.ofReal CS * xNorm c (-m) f)) :=
          mul_le_mul' le_rfl hsumle
      _ = ENNReal.ofReal (2 * CK * CS) * xNorm c (-m) f := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by norm_num)]
          simp only [ENNReal.ofReal_ofNat]
          ring
  have hxf : xNorm c (-m) f ≠ ⊤ := hf0.eLpNorm_ne_top
  have hHtop : h1Norm c m χ0 gχ ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hxf) hH
  obtain ⟨hxχ, hxg⟩ := xNorm_le_h1Norm_both c m χ0 gχ
  have hmem : ∀ φ : ℝ × ℝ → ℂ, AEStronglyMeasurable φ (volume.restrict (B0579.cell c)) →
      xNorm c (-m) φ ≠ ⊤ → MemLp (perRep c φ) 2 (B0579.cellMeasure c (-m)) := by
    intro φ hφ hne
    have hae := perRep_ae_cellMeasure hc0 (-m) φ
    refine ⟨?_, ?_⟩
    · exact ((hφ.mono_ac (B0579.cellMeasure_ac c (-m))).congr hae.symm)
    · rw [eLpNorm_congr_ae hae]
      exact lt_top_iff_ne_top.2 hne
  have hpt : ∀ x : ℝ × ℝ, ∀ u : Fin 2 → ℝ,
      f x * ((u 0 * B 0 x + u 1 * B 1 x : ℝ) : ℂ) = F 0 x * (u 0 : ℂ) + F 1 x * (u 1 : ℂ) := by
    intro x u
    simp only [hF]
    push_cast
    ring
  have hnX : ∀ φ : ℝ × ℝ → ℂ, xNorm c (-m) (perRep c φ) = xNorm c (-m) φ := fun φ =>
    eLpNorm_congr_ae (perRep_ae_cellMeasure hc0 (-m) φ)
  have hbd : xNorm c (-m) χ0 ≤ ENNReal.ofReal (2 * CK * CS) * jetNorm c m 0 D ∧
      ∀ j, xNorm c (-m) (gχ j) ≤ ENNReal.ofReal (2 * CK * CS) * jetNorm c m 0 D := by
    rw [hjet]
    exact ⟨hxχ.trans hH, fun j => (hxg j).trans hH⟩
  have hper : ∀ φ : ℝ × ℝ → ℂ, ∀ x : ℝ × ℝ, perRep c φ (x.1 + c, x.2) = perRep c φ x :=
    fun φ x => perRep_periodic hc0 φ x
  refine ⟨perRep c χ0, ktJet1 (perRep c χ0) (fun k => perRep c (gχ k)), ?_, ?_, ?_⟩
  · refine ⟨rfl, ?_, ?_, ?_⟩
    · intro w hw x
      match w, hw with
      | [], _ => exact hper _ x
      | [k], _ => exact hper (gχ k) x
      | _ :: _ :: _, hw => simp at hw
    · intro w hw
      match w, hw with
      | [], _ => exact hmem χ0 hmeas0 (ne_top_of_le_ne_top hHtop hxχ)
      | [k], _ => exact hmem (gχ k) (hmeasg k) (ne_top_of_le_ne_top hHtop (hxg k))
      | _ :: _ :: _, hw => simp at hw
    · intro j w hw
      match w, hw with
      | [], _ =>
        exact hCong c j χ0 (gχ j) _ _ (hweak j) (perRep_ae_cell hc0 χ0)
          (perRep_ae_cell hc0 (gχ j))
      | _ :: _, hw => simp at hw
  · intro w hw
    match w, hw with
    | [], _ => show xNorm c (-m) (perRep c χ0) ≤ _
               rw [hnX]; exact hbd.1
    | [k], _ => show xNorm c (-m) (perRep c (gχ k)) ≤ _
                rw [hnX]; exact hbd.2 k
    | _ :: _ :: _, hw => simp at hw
  · intro ψ uψ hψ hu
    have hi := hP c F (fun l => ⟨(hFs l).1, (hFs l).2.1⟩) ψ uψ hψ hu
    have hpr := hpair ψ uψ hψ hu
    have hfun : (fun x => f x * ((uψ x 0 * B 0 x + uψ x 1 * B 1 x : ℝ) : ℂ)) =
        fun x => F 0 x * (uψ x 0 : ℂ) + F 1 x * (uψ x 1 : ℂ) := funext fun x => hpt x _
    refine ⟨by rw [hfun]; exact hi, ?_⟩
    rw [hfun]
    calc ∫ x in B0579.cell c, perRep c χ0 x * (ψ x : ℂ)
        = ∫ x in B0579.cell c, χ0 x * (ψ x : ℂ) := by
          refine setIntegral_congr_fun (B0579.measurableSet_cell c) fun x hx => ?_
          rw [perRep_of_mem_cell hc0 χ0 hx]
      _ = ∫ x in B0579.cell c, ∑ j, F j x * ((uψ x j : ℝ) : ℂ) := hpr
      _ = _ := by simp [Fin.sum_univ_two]

theorem ktOrderMinusOneUnif_local (m : ℝ) : KTOrderMinusOneUnif m := by
  have hBase : KTBaseU m := ktBaseU_of m (kernelAdjointBound m) _root_.ktSource
    UnforcedLeray.Short.IIIa.ktPairInt UnforcedLeray.Short.IIIa.ktWeakMeas _root_.ktWeakCong
  have hComm : KTCommute m := ktCommute_of m _root_.ktSource _root_.ktCoeffDeriv
    _root_.ktWeakLeibniz UnforcedLeray.Short.IIIa.ktWeakIBP
    UnforcedLeray.Short.IIIa.kerVelSmooth UnforcedLeray.Short.IIIa.kerVelIsBS _root_.ktTestInt
  intro hm c hc j A
  have : ∀ j, KTAtU m c j := by
    intro j
    induction j with
    | zero => exact hBase hm c hc
    | succ j ih => exact ktAtU_succ hm hc hBase hComm _root_.ktCoeffDeriv _root_.ktWeakAdd j ih
  obtain ⟨C, hC0, H⟩ := this j A
  exact ⟨C, hC0, fun B hB hBp hBb f D hJ => H B hB hBp hBb f D hJ⟩

lemma dir_norm_le (l : Fin 2) : ‖B0579.dir l‖ ≤ 1 := by
  fin_cases l <;> simp [B0579.dir, Prod.norm_def]

lemma contDiff_pd {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (l : Fin 2) :
    ContDiff ℝ ∞ (B0579.pd l f) :=
  ((contDiff_infty_iff_fderiv.1 hf).2).clm_apply contDiff_const

lemma norm_iteratedFDeriv_pd_le {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (l : Fin 2)
    (n : ℕ) (x : ℝ × ℝ) :
    ‖iteratedFDeriv ℝ n (B0579.pd l f) x‖ ≤ ‖iteratedFDeriv ℝ (n + 1) f x‖ := by
  have h1 : ‖iteratedFDeriv ℝ n (B0579.pd l f) x‖ ≤
      ‖B0579.dir l‖ * ‖iteratedFDeriv ℝ (n + 1) f x‖ := by
    have := norm_iteratedFDeriv_clm_apply_const (f := fderiv ℝ f)
      (c := B0579.dir l) (x := x) (n := n)
      ((contDiff_infty_iff_fderiv.1 hf).2.contDiffAt) (by simp)
    rw [norm_iteratedFDeriv_fderiv] at this
    exact this
  exact h1.trans (mul_le_of_le_one_left (norm_nonneg _) (dir_norm_le l))

lemma norm_iteratedFDeriv_proj_le (v : ℝ × ℝ → EuclideanSpace ℝ (Fin 2)) (hv : ContDiff ℝ ∞ v)
    (j : Fin 2) (n : ℕ) (x : ℝ × ℝ) :
    ‖iteratedFDeriv ℝ n (fun w => v w j) x‖ ≤ ‖iteratedFDeriv ℝ n v x‖ := by
  let L : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ := EuclideanSpace.proj j
  have hL : ‖L‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun y => ?_)
    rw [one_mul]
    exact PiLp.norm_apply_le y j
  have hn : ContDiffAt ℝ ∞ v x := hv.contDiffAt
  have hle : (n : ℕ∞ω) ≤ (∞ : ℕ∞ω) := by simp
  have h := L.norm_iteratedFDeriv_comp_left hn hle
  calc ‖iteratedFDeriv ℝ n (fun w => v w j) x‖ = ‖iteratedFDeriv ℝ n (L ∘ v) x‖ := rfl
    _ ≤ ‖L‖ * ‖iteratedFDeriv ℝ n v x‖ := h
    _ ≤ 1 * ‖iteratedFDeriv ℝ n v x‖ := mul_le_mul_of_nonneg_right hL (norm_nonneg _)
    _ = ‖iteratedFDeriv ℝ n v x‖ := one_mul _

lemma Ec_eq_pd_sub {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) {ρ : ℝ} (hρ0 : 0 ≤ ρ) :
    UnforcedLeray.B0238.Ec tr ρ =
      fun z => B0579.pd 0 (fun w => tr.v ρ w 1) z - B0579.pd 1 (fun w => tr.v ρ w 0) z := by
  have hv : ContDiff ℝ ∞ (tr.v ρ) := UnforcedLeray.B0238.contDiff_Vc tr hρ0
  have hv1 : ContDiff ℝ 1 (tr.v ρ) := hv.of_le (by simp)
  funext z
  unfold UnforcedLeray.B0238.Ec
  rw [UnforcedLeray.B0238.curl_eq_fderiv hv1 z]
  simp [B0579.pd, B0579.dir]

lemma contDiff_Ec_slice {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) {ρ : ℝ} (hρ0 : 0 ≤ ρ) :
    ContDiff ℝ ∞ (UnforcedLeray.B0238.Ec tr ρ) := by
  have hv : ContDiff ℝ ∞ (tr.v ρ) := UnforcedLeray.B0238.contDiff_Vc tr hρ0
  have hf1 : ContDiff ℝ ∞ (fun w => tr.v ρ w 1) :=
    (EuclideanSpace.proj (1 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff.comp hv
  have hf0 : ContDiff ℝ ∞ (fun w => tr.v ρ w 0) :=
    (EuclideanSpace.proj (0 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff.comp hv
  rw [Ec_eq_pd_sub tr hρ0]
  exact (contDiff_pd hf1 0).sub (contDiff_pd hf0 1)

lemma periodic_pd_Ec {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) {ρ : ℝ} (hρ0 : 0 ≤ ρ)
    (l : Fin 2) (x : ℝ × ℝ) :
    B0579.pd l (UnforcedLeray.B0238.Ec tr ρ) (x.1 + c, x.2) =
      B0579.pd l (UnforcedLeray.B0238.Ec tr ρ) x := by
  have hper : ∀ z : ℝ × ℝ,
      UnforcedLeray.B0238.Ec tr ρ (z.1 + c, z.2) = UnforcedLeray.B0238.Ec tr ρ z := by
    intro z
    have hp1 : UnforcedLeray.Cyl.IsPeriodic c (fun w : ℝ × ℝ => tr.v ρ w 1) :=
      fun w => congrArg (fun u => u 1) (tr.isTrain.periodic_v ρ hρ0 w)
    have hp0 : UnforcedLeray.Cyl.IsPeriodic c (fun w : ℝ × ℝ => tr.v ρ w 0) :=
      fun w => congrArg (fun u => u 0) (tr.isTrain.periodic_v ρ hρ0 w)
    unfold UnforcedLeray.B0238.Ec UnforcedLeray.Cyl.curl
    rw [hp1.partialQ z, hp0.partialEta z]
  have hfun : (fun y : ℝ × ℝ => UnforcedLeray.B0238.Ec tr ρ (y + ((c : ℝ), (0 : ℝ)))) =
      UnforcedLeray.B0238.Ec tr ρ := by
    funext y
    have e : y + ((c : ℝ), (0 : ℝ)) = (y.1 + c, y.2) := by ext <;> simp
    rw [e]
    exact hper y
  have hk : fderiv ℝ (UnforcedLeray.B0238.Ec tr ρ) (x + ((c : ℝ), (0 : ℝ))) =
      fderiv ℝ (UnforcedLeray.B0238.Ec tr ρ) x := by
    have := fderiv_comp_add_right (𝕜 := ℝ) (f := UnforcedLeray.B0238.Ec tr ρ)
      (a := ((c : ℝ), (0 : ℝ))) (x := x)
    rw [hfun] at this
    exact this.symm
  unfold B0579.pd
  have e2 : ((x.1 + c, x.2) : ℝ × ℝ) = x + ((c : ℝ), (0 : ℝ)) := by ext <;> simp
  rw [e2, hk]

lemma norm_iteratedFDeriv_pd_Ec_le {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c)
    {ρ : ℝ} (hρ0 : 0 ≤ ρ) (l : Fin 2) (i : ℕ) (x : ℝ × ℝ) :
    ‖iteratedFDeriv ℝ i (B0579.pd l (UnforcedLeray.B0238.Ec tr ρ)) x‖ ≤
      2 * ‖iteratedFDeriv ℝ (i + 2) (tr.v ρ) x‖ := by
  have hv : ContDiff ℝ ∞ (tr.v ρ) := UnforcedLeray.B0238.contDiff_Vc tr hρ0
  have hf1 : ContDiff ℝ ∞ (fun w => tr.v ρ w 1) :=
    (EuclideanSpace.proj (1 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff.comp hv
  have hf0 : ContDiff ℝ ∞ (fun w => tr.v ρ w 0) :=
    (EuclideanSpace.proj (0 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff.comp hv
  have hEc := contDiff_Ec_slice tr hρ0
  have h1 := norm_iteratedFDeriv_pd_le hEc l i x
  have hsub : iteratedFDeriv ℝ (i + 1) (UnforcedLeray.B0238.Ec tr ρ) x =
      iteratedFDeriv ℝ (i + 1) (B0579.pd 0 (fun w => tr.v ρ w 1)) x -
        iteratedFDeriv ℝ (i + 1) (B0579.pd 1 (fun w => tr.v ρ w 0)) x := by
    rw [Ec_eq_pd_sub tr hρ0]
    exact iteratedFDeriv_sub_apply ((contDiff_pd hf1 0).contDiffAt.of_le (by simp))
      ((contDiff_pd hf0 1).contDiffAt.of_le (by simp))
  have h2 : ‖iteratedFDeriv ℝ (i + 1) (UnforcedLeray.B0238.Ec tr ρ) x‖ ≤
      ‖iteratedFDeriv ℝ (i + 1) (B0579.pd 0 (fun w => tr.v ρ w 1)) x‖ +
        ‖iteratedFDeriv ℝ (i + 1) (B0579.pd 1 (fun w => tr.v ρ w 0)) x‖ := by
    rw [hsub]
    exact norm_sub_le _ _
  have ha1 := (norm_iteratedFDeriv_pd_le hf1 0 (i + 1) x).trans
    (norm_iteratedFDeriv_proj_le (tr.v ρ) hv 1 (i + 2) x)
  have ha0 := (norm_iteratedFDeriv_pd_le hf0 1 (i + 1) x).trans
    (norm_iteratedFDeriv_proj_le (tr.v ρ) hv 0 (i + 2) x)
  linarith [h1, h2, ha1, ha0]

lemma contDiff_ladChi {ν c t s ρ : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c)
    {φ : ℝ → ℝ × ℝ → ℂ} (ht : 0 ≤ t)
    (hj : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (Ico t s ×ˢ univ))
    (hρ : ρ ∈ Ioo t s) : ContDiff ℝ ∞ (ladChi tr φ ρ) := by
  have hslice : ContDiff ℝ ∞ (φ ρ) := adjContDiff_slice hj (Ioo_subset_Ico_self hρ)
  have hdt : ContDiff ℝ ∞ (ladDt φ ρ) := LadDtReg.contDiff_ladDt_of hj hρ
  have hlap : ContDiff ℝ ∞ (ladLapCx (φ ρ)) := by
    unfold ladLapCx
    exact (contDiff_pdCx (contDiff_pdCx hslice 0) 0).add (contDiff_pdCx (contDiff_pdCx hslice 1) 1)
  have hv : ∀ j : Fin 2, ContDiff ℝ ∞ (fun x : ℝ × ℝ => ((tr.v ρ x j : ℝ) : ℂ)) := by
    intro j
    have h : ContDiff ℝ ∞ (fun w => tr.v ρ w j) :=
      (EuclideanSpace.proj j : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff.comp
        (UnforcedLeray.B0238.contDiff_Vc tr (ht.trans hρ.1.le))
    exact Complex.ofRealCLM.contDiff.comp h
  have htr : ContDiff ℝ ∞ (ladTransport tr ρ (φ ρ)) := by
    unfold ladTransport
    exact ((hv 0).mul (contDiff_pdCx hslice 0)).add ((hv 1).mul (contDiff_pdCx hslice 1))
  have e : ladChi tr φ ρ = fun x => ladDt φ ρ x + (ν : ℂ) * ladLapCx (φ ρ) x +
      ladTransport tr ρ (φ ρ) x := rfl
  rw [e]
  exact (hdt.add (contDiff_const.mul hlap)).add htr

lemma periodic_ladChi {ν c t s ρ : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c)
    {φ : ℝ → ℝ × ℝ → ℂ} (ht : 0 ≤ t)
    (hj : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (Ico t s ×ˢ univ))
    (hper : ∀ r ∈ Ico t s, ∀ x : ℝ × ℝ, φ r (x.1 + c, x.2) = φ r x)
    (hρ : ρ ∈ Ioo t s) (x : ℝ × ℝ) :
    ladChi tr φ ρ (x.1 + c, x.2) = ladChi tr φ ρ x := by
  have hρ' : ρ ∈ Ico t s := Ioo_subset_Ico_self hρ
  have hρ0 : 0 ≤ ρ := ht.trans hρ.1.le
  have hdt : ladDt φ ρ (x.1 + c, x.2) = ladDt φ ρ x :=
    (ladDtRegular c t s φ hj hper ρ hρ).2 x
  have hp_w : ∀ w : List (Fin 2), adjSpatial w (φ ρ) (x.1 + c, x.2) = adjSpatial w (φ ρ) x :=
    fun w => HigherContAux.periodic_adjSpatial (hper ρ hρ') w x
  have hlap : ladLapCx (φ ρ) (x.1 + c, x.2) = ladLapCx (φ ρ) x := by
    unfold ladLapCx
    have h00 := hp_w [0, 0]
    have h11 := hp_w [1, 1]
    simpa [adjSpatial] using congrArg₂ (· + ·) h00 h11
  have htr : ladTransport tr ρ (φ ρ) (x.1 + c, x.2) = ladTransport tr ρ (φ ρ) x := by
    unfold ladTransport
    have hv0 : tr.v ρ (x.1 + c, x.2) 0 = tr.v ρ x 0 :=
      congrArg (fun u => u 0) (tr.isTrain.periodic_v ρ hρ0 x)
    have hv1 : tr.v ρ (x.1 + c, x.2) 1 = tr.v ρ x 1 :=
      congrArg (fun u => u 1) (tr.isTrain.periodic_v ρ hρ0 x)
    have hp0 : pdCx 0 (φ ρ) (x.1 + c, x.2) = pdCx 0 (φ ρ) x := hp_w [0]
    have hp1 : pdCx 1 (φ ρ) (x.1 + c, x.2) = pdCx 1 (φ ρ) x := hp_w [1]
    rw [hv0, hv1, hp0, hp1]
  unfold ladChi
  rw [hdt, hlap, htr]

end ChiBoundAux

open ChiBoundAux in
/-- **(ii) Weighted `X_{-m,c}` bound on `∂^w χ` from the train jets**
(`PartIII-a:T21/2/7/2/4/1`, SP lines 3052-3058, 3060-3073). -/
theorem adjHigherChiBound (m : ℝ) (hm : 8 < m) : UnforcedLeray.Short.IIIa.AdjHigherChiBound m := by
  intro ν hν hν1 tr hb hJ t s ht hts G hG φ hφ hj k hk hcont b hbI
  let c : ℝ := ν ^ (-2 : ℝ)
  have hc0 : 0 < c := Real.rpow_pos_of_pos hν _
  have hc1 : 1 ≤ c := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hν hν1 (by norm_num)
  have hm1 : 1 < m := by linarith
  have hb0 : 0 ≤ b := ht.trans hbI.1.le
  obtain ⟨CJ, hCJ⟩ := hJ b hb0
  obtain ⟨CKT, hCKT0, hKT⟩ := ktOrderMinusOneUnif_local m hm1 c hc1 k (2 * |CJ|)
  have hex_w : ∀ w : List (Fin 2), ∃ Mw : ℝ, 0 ≤ Mw ∧ ∀ ρ ∈ Ioo t b,
      w.length ≤ k → xNorm c (-m) (adjSpatial w (φ ρ)) ≤ ENNReal.ofReal Mw := by
    intro w
    by_cases hw : w.length ≤ k
    · obtain ⟨M₀, hM₀⟩ := HigherContAux.exists_xNorm_bdd_on_Ioo hbI
        (fun r hr => (hcont r hr w hw).1) (fun r hr => (hcont r hr w hw).2)
      refine ⟨max M₀ 0, le_max_right _ _, fun ρ hρ _ => ?_⟩
      exact (hM₀ ρ hρ).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
    · exact ⟨0, le_rfl, fun _ _ h => absurd h hw⟩
  choose Mw hMw0 hMw using hex_w
  set Mjet : ℝ := ∑ w ∈ wordsLE k, Mw w
  have hMjet0 : 0 ≤ Mjet := Finset.sum_nonneg fun w _ => hMw0 w
  refine ⟨CKT * Mjet, fun ρ hρ => ?_⟩
  have hρs : ρ ∈ Ioo t s := ⟨hρ.1, hρ.2.trans hbI.2⟩
  have hρIco : ρ ∈ Ico t s := Ioo_subset_Ico_self hρs
  have hρb : ρ ∈ Icc (0 : ℝ) b := ⟨ht.trans hρ.1.le, hρ.2.le⟩
  have hρ0 : 0 ≤ ρ := hρb.1
  have hBs : ∀ l : Fin 2, ContDiff ℝ ∞ (B0579.pd l (UnforcedLeray.B0238.Ec tr ρ)) :=
    fun l => contDiff_pd (contDiff_Ec_slice tr hρ0) l
  have hBp : ∀ (l : Fin 2) (x : ℝ × ℝ),
      B0579.pd l (UnforcedLeray.B0238.Ec tr ρ) (x.1 + c, x.2) =
        B0579.pd l (UnforcedLeray.B0238.Ec tr ρ) x :=
    fun l x => periodic_pd_Ec tr hρ0 l x
  have hBb : ∀ (l : Fin 2) (i : ℕ), i ≤ k → ∀ x : ℝ × ℝ,
      (1 + x.2 ^ 2) ^ ((m + 1) / 2) *
        ‖iteratedFDeriv ℝ i (B0579.pd l (UnforcedLeray.B0238.Ec tr ρ)) x‖ ≤ 2 * |CJ| := by
    intro l i hi x
    set kw : ℕ := ⌈max 0 ((m + 2) / 2)⌉₊
    have h1x : 1 ≤ 1 + x.2 ^ 2 := by nlinarith [sq_nonneg x.2]
    have hexp : (m + 1) / 2 ≤ (kw : ℝ) := by
      have h1 : (m + 1) / 2 ≤ (m + 2) / 2 := by linarith
      exact h1.trans ((le_max_right 0 _).trans (Nat.le_ceil _))
    have hw_le : (1 + x.2 ^ 2) ^ ((m + 1) / 2) ≤ (1 + x.2 ^ 2) ^ kw := by
      calc (1 + x.2 ^ 2) ^ ((m + 1) / 2) ≤ (1 + x.2 ^ 2) ^ (kw : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le h1x hexp
        _ = (1 + x.2 ^ 2) ^ kw := Real.rpow_natCast _ _
    have hd_le := norm_iteratedFDeriv_pd_Ec_le tr hρ0 l i x
    have hi6 : i + 2 ≤ 6 := by omega
    have htr_bd : (1 + x.2 ^ 2) ^ kw * ‖iteratedFDeriv ℝ (i + 2) (tr.v ρ) x‖ ≤ |CJ| :=
      (hCJ (i + 2) hi6 ρ hρb x).trans (le_abs_self CJ)
    calc (1 + x.2 ^ 2) ^ ((m + 1) / 2) *
          ‖iteratedFDeriv ℝ i (B0579.pd l (UnforcedLeray.B0238.Ec tr ρ)) x‖
        ≤ (1 + x.2 ^ 2) ^ kw * (2 * ‖iteratedFDeriv ℝ (i + 2) (tr.v ρ) x‖) :=
          mul_le_mul hw_le hd_le (norm_nonneg _) (by positivity)
      _ = 2 * ((1 + x.2 ^ 2) ^ kw * ‖iteratedFDeriv ℝ (i + 2) (tr.v ρ) x‖) := by ring
      _ ≤ 2 * |CJ| := mul_le_mul_of_nonneg_left htr_bd (by norm_num)
  have hslice_φ : ContDiff ℝ ∞ (φ ρ) := adjContDiff_slice hj hρIco
  have hper_φ : ∀ x : ℝ × ℝ, φ ρ (x.1 + c, x.2) = φ ρ x :=
    fun x => hφ.periodic ρ hρIco x
  have hJφ : IsCellJet c m k (φ ρ) (fun w => adjSpatial w (φ ρ)) := by
    refine ⟨rfl, ?_, ?_, ?_⟩
    · intro w _ x
      exact HigherContAux.periodic_adjSpatial hper_φ w x
    · intro w hw
      exact (hcont ρ hρIco w hw).1
    · intro j w hw
      exact ibpPdCxWeak c j (adjSpatial w (φ ρ)) hc0 (contDiff_adjSpatial hslice_φ w)
        (HigherContAux.periodic_adjSpatial hper_φ w)
  have hjet_le : jetNorm c m k (fun w => adjSpatial w (φ ρ)) ≤ ENNReal.ofReal Mjet := by
    unfold jetNorm Mjet
    rw [ENNReal.ofReal_sum_of_nonneg (fun w _ => hMw0 w)]
    refine Finset.sum_le_sum fun w hw => ?_
    exact hMw w ρ hρ (mem_wordsLE.1 hw)
  obtain ⟨χ', Dχ', hJχ, hbdχ, hpairχ⟩ :=
    hKT (fun l => B0579.pd l (UnforcedLeray.B0238.Ec tr ρ)) hBs hBp hBb
      (φ ρ) (fun w => adjSpatial w (φ ρ)) hJφ
  have hderχ : ∀ j : Fin 2, HasWeakCellDerivC c j χ' (Dχ' [j]) := by
    intro j
    have h := hJχ.deriv j [] (Nat.succ_pos k)
    rwa [hJχ.base] at h
  have hfinχ : h1Norm c m χ' (fun j => Dχ' [j]) ≠ ⊤ := by
    unfold h1Norm
    have h0 : xNorm c (-m) χ' < ⊤ := by
      have hm0 := hJχ.memX [] (Nat.zero_le _)
      rw [hJχ.base] at hm0
      exact hm0.2
    have h1 : ∀ j : Fin 2, xNorm c (-m) (Dχ' [j]) < ⊤ :=
      fun j => (hJχ.memX [j] (by simp)).2
    have hsum : xNorm c (-m) χ' ^ 2 + ∑ j : Fin 2, xNorm c (-m) (Dχ' [j]) ^ 2 < ⊤ := by
      rw [Fin.sum_univ_two]
      exact ENNReal.add_lt_top.2 ⟨ENNReal.pow_lt_top h0,
        ENNReal.add_lt_top.2 ⟨ENNReal.pow_lt_top (h1 0), ENNReal.pow_lt_top (h1 1)⟩⟩
    exact (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hsum.ne).ne
  have hctx : AdjWCtx m ν c tr t s (physAdj (clockA ν s) G) φ :=
    ⟨hν, hc0, ht, hts, hb, hφ, hj⟩
  have hae : ladChi tr φ ρ =ᵐ[volume.restrict (B0579.cell c)] χ' := by
    refine adjWChiIdentify m hm ν c tr t s (physAdj (clockA ν s) G) φ hc1 hctx ρ hρs
      χ' (fun j => Dχ' [j]) hderχ hfinχ ?_
    intro ψ uψ hψ hu
    rw [(hpairχ ψ uψ hψ hu).2]
    refine setIntegral_congr_fun (B0579.measurableSet_cell c) fun y _ => ?_
    simp only [Fin.sum_univ_two]
    push_cast
    ring
  have hsm_χ : ContDiff ℝ ∞ (ladChi tr φ ρ) := contDiff_ladChi tr ht hj hρs
  have hper_χ : ∀ x : ℝ × ℝ, ladChi tr φ ρ (x.1 + c, x.2) = ladChi tr φ ρ x :=
    fun x => periodic_ladChi tr ht hj hφ.periodic hρs x
  have hcell : ∀ w : List (Fin 2), w.length ≤ k + 1 →
      adjSpatial w (ladChi tr φ ρ) =ᵐ[volume.restrict (B0579.cell c)] Dχ' w := by
    intro w
    induction w with
    | nil =>
      intro _
      rw [hJχ.base]
      exact hae
    | cons j w ih =>
      intro hw
      have hlt : w.length < k + 1 := by simpa using hw
      have h1 := ibpPdCxWeak c j (adjSpatial w (ladChi tr φ ρ)) hc0
        (contDiff_adjSpatial hsm_χ w) (HigherContAux.periodic_adjSpatial hper_χ w)
      have h1' : HasWeakCellDerivC c j (Dχ' w) (adjSpatial (j :: w) (ladChi tr φ ρ)) :=
        HasWeakCellDerivC.congr_ae (ih hlt.le).symm (Eventually.of_forall fun _ => rfl) h1
      exact weakCellAeUnique c j (Dχ' w) _ _ h1' (hJχ.deriv j w hlt)
  intro w hw
  have hae_cm : adjSpatial w (ladChi tr φ ρ) =ᵐ[B0579.cellMeasure c (-m)] Dχ' w :=
    (B0579.cellMeasure_ac c (-m)) (hcell w hw)
  refine ⟨(hJχ.memX w hw).ae_eq hae_cm.symm, ?_⟩
  rw [eLpNorm_congr_ae hae_cm]
  calc xNorm c (-m) (Dχ' w)
      ≤ ENNReal.ofReal CKT * jetNorm c m k (fun u => adjSpatial u (φ ρ)) := hbdχ w hw
    _ ≤ ENNReal.ofReal CKT * ENNReal.ofReal Mjet := mul_le_mul' le_rfl hjet_le
    _ = ENNReal.ofReal (CKT * Mjet) := (ENNReal.ofReal_mul hCKT0).symm

end UnforcedLeray.Short.IIIa
