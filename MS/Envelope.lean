import MS.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Topology.Order.Monotone

set_option linter.style.haveILetI false

open MeasureTheory Filter TopologicalSpace
open scoped Topology

namespace MSData

theorem Q_mono (D : MSData) : MonotoneOn (fun v => D.Q v) (Set.Icc D.a1 D.b1) := by
  intro v hv v' hv' hvv'
  have h₁ := D.bicB' v hv v' hv'
  have h₂ := D.bicB' v' hv' v hv
  have hprod : 0 ≤ (v' - v) * (D.Q v' - D.Q v) := by
    nlinarith [h₁, h₂]
  by_contra hq
  have hq' : D.Q v' < D.Q v := lt_of_not_ge hq
  rcases hvv'.eq_or_lt with hEq | hlt
  · subst v'
    exact (lt_irrefl _ hq')
  · have hneg : (v' - v) * (D.Q v' - D.Q v) < 0 :=
      mul_neg_of_pos_of_neg (sub_pos.mpr hlt) (sub_neg.mpr hq')
    linarith

theorem R_anti (D : MSData) : AntitoneOn (fun c => D.R c) (Set.Icc D.a2 D.b2) := by
  intro c hc c' hc' hcc'
  have h₁ := D.bicS' c hc c' hc'
  have h₂ := D.bicS' c' hc' c hc
  have hprod : 0 ≤ (c' - c) * (D.R c - D.R c') := by
    nlinarith [h₁, h₂]
  by_contra hR
  have hR' : D.R c < D.R c' := lt_of_not_ge hR
  rcases hcc'.eq_or_lt with hEq | hlt
  · subst c'
    exact (lt_irrefl _ hR')
  · have hneg : (c' - c) * (D.R c - D.R c') < 0 :=
      mul_neg_of_pos_of_neg (sub_pos.mpr hlt) (sub_neg.mpr hR')
    linarith

theorem Q_nonneg (D : MSData) (v : ℝ) (hv : v ∈ Set.Icc D.a1 D.b1) : 0 ≤ D.Q v := by
  rw [Q_def, interimQ]
  apply integral_nonneg_of_ae
  filter_upwards [D.nu.support_mem_ae] with c hc
  exact D.q_nonneg v hv c (D.nu_supported hc)

theorem Q_le_one (D : MSData) (v : ℝ) (hv : v ∈ Set.Icc D.a1 D.b1) : D.Q v ≤ 1 := by
  letI : IsProbabilityMeasure D.nu := D.nu_probability
  have hrange : ∀ᵐ c ∂D.nu, D.q (v, c) ∈ Set.Icc 0 1 := by
    filter_upwards [D.nu.support_mem_ae] with c hc
    exact ⟨D.q_nonneg v hv c (D.nu_supported hc), D.q_le_one v hv c (D.nu_supported hc)⟩
  have hqint : Integrable (fun c => D.q (v, c)) D.nu := by
    exact (memLp_of_bounded hrange (D.q_sectionB v hv) 1).integrable (by norm_num)
  have hle := integral_mono_ae hqint (integrable_const (1 : ℝ)) <| by
    filter_upwards [D.nu.support_mem_ae] with c hc
    exact D.q_le_one v hv c (D.nu_supported hc)
  rw [Q_def, interimQ]
  simpa [integral_const] using hle

theorem R_nonneg (D : MSData) (c : ℝ) (hc : c ∈ Set.Icc D.a2 D.b2) : 0 ≤ D.R c := by
  rw [R_def, interimR]
  apply integral_nonneg_of_ae
  filter_upwards [D.mu.support_mem_ae] with v hv
  exact D.q_nonneg v (D.mu_supported hv) c hc

theorem R_le_one (D : MSData) (c : ℝ) (hc : c ∈ Set.Icc D.a2 D.b2) : D.R c ≤ 1 := by
  letI : IsProbabilityMeasure D.mu := D.mu_probability
  have hrange : ∀ᵐ v ∂D.mu, D.q (v, c) ∈ Set.Icc 0 1 := by
    filter_upwards [D.mu.support_mem_ae] with v hv
    exact ⟨D.q_nonneg v (D.mu_supported hv) c hc, D.q_le_one v (D.mu_supported hv) c hc⟩
  have hqint : Integrable (fun v => D.q (v, c)) D.mu := by
    exact (memLp_of_bounded hrange (D.q_sectionS c hc) 1).integrable (by norm_num)
  have hle := integral_mono_ae hqint (integrable_const (1 : ℝ)) <| by
    filter_upwards [D.mu.support_mem_ae] with v hv
    exact D.q_le_one v (D.mu_supported hv) c hc
  rw [R_def, interimR]
  simpa [integral_const] using hle

theorem U_lip (D : MSData) (v : ℝ) (hv : v ∈ Set.Icc D.a1 D.b1)
    (v' : ℝ) (hv' : v' ∈ Set.Icc D.a1 D.b1) :
    |D.U v - D.U v'| ≤ |v - v'| := by
  let x := v - v'
  let d := D.U v - D.U v'
  have hq₁ := D.Q_nonneg v' hv'
  have hq₂ := D.Q_le_one v' hv'
  have hq₃ := D.Q_nonneg v hv
  have hq₄ := D.Q_le_one v hv
  have hp₁ : |x * D.Q v'| ≤ |x| := by
    rw [abs_mul, abs_of_nonneg hq₁]
    exact mul_le_of_le_one_right (abs_nonneg x) hq₂
  have hp₂ : |x * D.Q v| ≤ |x| := by
    rw [abs_mul, abs_of_nonneg hq₃]
    exact mul_le_of_le_one_right (abs_nonneg x) hq₄
  have h₁ := D.bicB' v hv v' hv'
  have h₂ := D.bicB' v' hv' v hv
  have hlo : x * D.Q v' ≤ d := by
    change (v - v') * D.Q v' ≤ D.U v - D.U v'
    apply (le_sub_iff_add_le).2
    simpa [add_comm] using h₁
  have hhi : d ≤ x * D.Q v := by
    change D.U v - D.U v' ≤ (v - v') * D.Q v
    apply (sub_le_iff_le_add).2
    have hh : D.U v ≤ (v - v') * D.Q v + D.U v' := by linarith [h₂]
    exact hh
  apply (abs_le).2
  constructor
  · calc
      -|x| ≤ -|x * D.Q v'| := neg_le_neg hp₁
      _ ≤ x * D.Q v' := neg_abs_le _
      _ ≤ d := hlo
  · calc
      d ≤ x * D.Q v := hhi
      _ ≤ |x * D.Q v| := le_abs_self _
      _ ≤ |x| := hp₂

theorem W_lip (D : MSData) (c : ℝ) (hc : c ∈ Set.Icc D.a2 D.b2)
    (c' : ℝ) (hc' : c' ∈ Set.Icc D.a2 D.b2) :
    |D.W c - D.W c'| ≤ |c - c'| := by
  let x := c - c'
  let d := D.W c - D.W c'
  have hR₁ := D.R_nonneg c' hc'
  have hR₂ := D.R_le_one c' hc'
  have hR₃ := D.R_nonneg c hc
  have hR₄ := D.R_le_one c hc
  have hp₁ : |(-x) * D.R c'| ≤ |x| := by
    rw [abs_mul, abs_of_nonneg hR₁, abs_neg]
    exact mul_le_of_le_one_right (abs_nonneg x) hR₂
  have hp₂ : |(-x) * D.R c| ≤ |x| := by
    rw [abs_mul, abs_of_nonneg hR₃, abs_neg]
    exact mul_le_of_le_one_right (abs_nonneg x) hR₄
  have h₁ := D.bicS' c hc c' hc'
  have h₂ := D.bicS' c' hc' c hc
  have hlo : (-x) * D.R c' ≤ d := by
    calc
      (-x) * D.R c' = (c' - c) * D.R c' := by dsimp [x]; ring
      _ ≤ D.W c - D.W c' := (le_sub_iff_add_le).2 (by simpa [add_comm] using h₁)
      _ = d := rfl
  have hhi : d ≤ (-x) * D.R c := by
    calc
      d = D.W c - D.W c' := rfl
      _ ≤ (c' - c) * D.R c := (sub_le_iff_le_add).2 (by nlinarith [h₂])
      _ = (-x) * D.R c := by dsimp [x]; congr 1; ring
  apply (abs_le).2
  constructor
  · calc
      -|x| ≤ -|(-x) * D.R c'| := neg_le_neg hp₁
      _ ≤ (-x) * D.R c' := neg_abs_le _
      _ ≤ d := hlo
  · calc
      d ≤ (-x) * D.R c := hhi
      _ ≤ |(-x) * D.R c| := le_abs_self _
      _ ≤ |x| := hp₂

private theorem hasDerivAt_of_monotone_subgradient
    {a b : ℝ} {f g : ℝ → ℝ}
    (hmono : MonotoneOn g (Set.Icc a b))
    (hsub : ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b,
      f x ≥ f y + (x - y) * g y)
    {x : ℝ} (hx : x ∈ Set.Ioo a b) (hgc : ContinuousAt g x) :
    HasDerivAt f (g x) x := by
  have hxIcc : x ∈ Set.Icc a b := ⟨hx.1.le, hx.2.le⟩
  have hnear : ∀ᶠ y in 𝓝[≠] x, y ∈ Set.Ioo a b :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (show ∀ᶠ y in 𝓝 x, y ∈ Set.Ioo a b from Ioo_mem_nhds hx.1 hx.2)
  have hbound : ∀ᶠ y in 𝓝[≠] x,
      |slope f x y - g x| ≤ |g y - g x| := by
    filter_upwards [hnear, self_mem_nhdsWithin] with y hy hyne
    have hyne : y ≠ x := by simpa using hyne
    have hyIcc : y ∈ Set.Icc a b := ⟨hy.1.le, hy.2.le⟩
    have hlow : (y - x) * g x ≤ f y - f x := by
      have hh := hsub y hyIcc x hxIcc
      linarith
    have hhigh : f y - f x ≤ (y - x) * g y := by
      have hh := hsub x hxIcc y hyIcc
      linarith
    have hslope : slope f x y = (f y - f x) / (y - x) := by
      rw [slope_def_field]
    by_cases hxy : x < y
    · have hp : 0 < y - x := sub_pos.mpr hxy
      have hmono' : g x ≤ g y := hmono hxIcc hyIcc hxy.le
      have hratio₁ : g x ≤ (f y - f x) / (y - x) :=
        (le_div_iff₀ hp).2 (by nlinarith [hlow])
      have hratio₂ : (f y - f x) / (y - x) ≤ g y :=
        (div_le_iff₀ hp).2 (by nlinarith [hhigh])
      rw [hslope, abs_of_nonneg (sub_nonneg.mpr hmono')]
      apply (abs_le).2
      constructor <;> nlinarith [hratio₁, hratio₂, hmono']
    · have hyx : y < x := lt_of_le_of_ne (le_of_not_gt hxy) hyne
      have hp : y - x < 0 := sub_neg.mpr hyx
      have hmono' : g y ≤ g x := hmono hyIcc hxIcc hyx.le
      have hratio₁ : g y ≤ (f y - f x) / (y - x) :=
        (le_div_iff_of_neg hp).2 (by nlinarith [hhigh])
      have hratio₂ : (f y - f x) / (y - x) ≤ g x :=
        (div_le_iff_of_neg hp).2 (by nlinarith [hlow])
      rw [hslope, abs_of_nonpos (sub_nonpos.mpr hmono')]
      apply (abs_le).2
      constructor <;> nlinarith [hratio₁, hratio₂, hmono']
  have hupper : Tendsto (fun y => |g y - g x|) (𝓝[≠] x) (𝓝 0) := by
    simpa using ((hgc.tendsto.mono_left nhdsWithin_le_nhds).sub_const (g x)).abs
  have hnorm : Tendsto (fun y => |slope f x y - g x|) (𝓝[≠] x) (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
      (Filter.Eventually.of_forall fun y => abs_nonneg _)
      hbound
  apply (hasDerivAt_iff_tendsto_slope).2
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simpa only [Real.norm_eq_abs] using hnorm

private theorem deriv_eq_ae_of_monotone_subgradient
    {a b : ℝ} {f g : ℝ → ℝ}
    (hmono : MonotoneOn g (Set.Icc a b))
    (hsub : ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b,
      f x ≥ f y + (x - y) * g y) :
    ∀ᵐ x ∂volume, x ∈ Set.Ioo a b → deriv f x = g x := by
  have hbad := hmono.countable_not_continuousWithinAt
  filter_upwards [hbad.ae_notMem volume] with x hx hxIoo
  have hxIcc : x ∈ Set.Icc a b := ⟨hxIoo.1.le, hxIoo.2.le⟩
  have hcontWithin : ContinuousWithinAt g (Set.Icc a b) x := by
    by_contra hcont
    exact hx ⟨hxIcc, hcont⟩
  have hcontAt : ContinuousAt g x :=
    hcontWithin.continuousAt (Icc_mem_nhds hxIoo.1 hxIoo.2)
  exact (hasDerivAt_of_monotone_subgradient hmono hsub hxIoo hcontAt).deriv

private theorem intervalIntegral_eq_sub_of_lipschitz_subgradient
    {a b : ℝ} (hab : a ≤ b) {f g : ℝ → ℝ}
    (hmono : MonotoneOn g (Set.Icc a b))
    (hsub : ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b,
      f x ≥ f y + (x - y) * g y)
    (hlip : LipschitzOnWith 1 f (Set.uIcc a b)) :
    f b - f a = ∫ x in a..b, g x := by
  have hac : AbsolutelyContinuousOnInterval f a b := hlip.absolutelyContinuousOnInterval
  have hftc : ∫ x in a..b, deriv f x = f b - f a := hac.integral_deriv_eq_sub
  have hderiv := deriv_eq_ae_of_monotone_subgradient hmono hsub
  have hcongr : ∫ x in a..b, deriv f x = ∫ x in a..b, g x := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hderiv, (Set.countable_singleton b).ae_notMem volume]
      with x hxderiv hxb hx
    have hxIoc : x ∈ Set.Ioc a b := by
      simpa [Set.uIoc_of_le hab] using hx
    have hxb : x < b := lt_of_le_of_ne hxIoc.2 (by simpa using hxb)
    exact hxderiv ⟨hxIoc.1, hxb⟩
  calc
    f b - f a = ∫ x in a..b, deriv f x := hftc.symm
    _ = ∫ x in a..b, g x := hcongr

theorem U_envelope (D : MSData) (v : ℝ) (hv : v ∈ Set.Icc D.a1 D.b1) :
    D.U v - D.U D.a1 = ∫ t in D.a1..v, D.Q t := by
  have hmono : MonotoneOn (fun t => D.Q t) (Set.Icc D.a1 v) := by
    intro x hx y hy hxy
    exact D.Q_mono ⟨hx.1, le_trans hx.2 hv.2⟩ ⟨hy.1, le_trans hy.2 hv.2⟩ hxy
  have hsub : ∀ x ∈ Set.Icc D.a1 v, ∀ y ∈ Set.Icc D.a1 v,
      D.U x ≥ D.U y + (x - y) * D.Q y := by
    intro x hx y hy
    exact D.bicB' x ⟨hx.1, le_trans hx.2 hv.2⟩ y ⟨hy.1, le_trans hy.2 hv.2⟩
  have hlip : LipschitzOnWith 1 D.U (Set.uIcc D.a1 v) :=
    LipschitzOnWith.mk_one fun x hx y hy => by
      have hxI : x ∈ Set.Icc D.a1 D.b1 := by
        have hx' : x ∈ Set.Icc D.a1 v := by simpa [Set.uIcc_of_le hv.1] using hx
        exact ⟨hx'.1, le_trans hx'.2 hv.2⟩
      have hyI : y ∈ Set.Icc D.a1 D.b1 := by
        have hy' : y ∈ Set.Icc D.a1 v := by simpa [Set.uIcc_of_le hv.1] using hy
        exact ⟨hy'.1, le_trans hy'.2 hv.2⟩
      simpa [Real.dist_eq] using D.U_lip x hxI y hyI
  exact intervalIntegral_eq_sub_of_lipschitz_subgradient hv.1 hmono hsub hlip

theorem W_envelope (D : MSData) (c : ℝ) (hc : c ∈ Set.Icc D.a2 D.b2) :
    D.W c - D.W D.b2 = ∫ t in c..D.b2, D.R t := by
  have hmono : MonotoneOn (fun t => -D.R t) (Set.Icc c D.b2) := by
    intro x hx y hy hxy
    have hR := D.R_anti ⟨le_trans hc.1 hx.1, hx.2⟩ ⟨le_trans hc.1 hy.1, hy.2⟩ hxy
    linarith
  have hsub : ∀ x ∈ Set.Icc c D.b2, ∀ y ∈ Set.Icc c D.b2,
      D.W x ≥ D.W y + (x - y) * (-D.R y) := by
    intro x hx y hy
    have hxy := D.bicS' x ⟨le_trans hc.1 hx.1, hx.2⟩ y ⟨le_trans hc.1 hy.1, hy.2⟩
    nlinarith [hxy]
  have hlip : LipschitzOnWith 1 D.W (Set.uIcc c D.b2) :=
    LipschitzOnWith.mk_one fun x hx y hy => by
      have hxI : x ∈ Set.Icc D.a2 D.b2 := by
        have hx' : x ∈ Set.Icc c D.b2 := by simpa [Set.uIcc_of_le hc.2] using hx
        exact ⟨le_trans hc.1 hx'.1, hx'.2⟩
      have hyI : y ∈ Set.Icc D.a2 D.b2 := by
        have hy' : y ∈ Set.Icc c D.b2 := by simpa [Set.uIcc_of_le hc.2] using hy
        exact ⟨le_trans hc.1 hy'.1, hy'.2⟩
      simpa [Real.dist_eq] using D.W_lip x hxI y hyI
  have hInt := intervalIntegral_eq_sub_of_lipschitz_subgradient hc.2 hmono hsub hlip
  calc
    D.W c - D.W D.b2 = -(D.W D.b2 - D.W c) := by ring
    _ = -(∫ t in c..D.b2, -D.R t) := by rw [hInt]
    _ = ∫ t in c..D.b2, D.R t := by rw [intervalIntegral.integral_neg]; ring

theorem EU_eq (D : MSData) :
    (∫ v, D.U v ∂D.mu) = D.U D.a1 +
      ∫ t in D.a1..D.b1, D.Q t * D.mu.real {v | t ≤ v} := by
  letI : IsProbabilityMeasure D.mu := D.mu_probability
  have hfullLip : LipschitzOnWith 1 D.U (Set.Icc D.a1 D.b1) :=
    LipschitzOnWith.mk_one fun v hv v' hv' => by
      simpa [Real.dist_eq] using D.U_lip v hv v' hv'
  have hUcont : ContinuousOn D.U (Set.Icc D.a1 D.b1) := hfullLip.continuousOn
  have hμIcc : ∀ᵐ v ∂D.mu, v ∈ Set.Icc D.a1 D.b1 := by
    filter_upwards [D.mu.support_mem_ae] with v hv
    exact D.mu_supported hv
  have hμrestrict : D.mu.restrict (Set.Icc D.a1 D.b1) = D.mu :=
    Measure.restrict_eq_self_of_ae_mem hμIcc
  have hUon : IntegrableOn D.U (Set.Icc D.a1 D.b1) D.mu :=
    hUcont.integrableOn_of_subset_isCompact isCompact_Icc measurableSet_Icc
      (by intro x hx; exact hx)
      (measure_ne_top D.mu (Set.Icc D.a1 D.b1))
  have hUint : Integrable D.U D.mu := by
    rw [← hμrestrict]
    exact hUon
  have hconst : ∫ _ : ℝ, D.U D.a1 ∂D.mu = D.U D.a1 := by simp
  have hdecomp : (∫ v, D.U v ∂D.mu) = D.U D.a1 +
      ∫ v, (D.U v - D.U D.a1) ∂D.mu := by
    rw [integral_sub hUint (integrable_const _), hconst]
    ring
  have hEnvAE : ∀ᵐ v ∂D.mu, D.U v - D.U D.a1 = ∫ t in D.a1..v, D.Q t := by
    filter_upwards [hμIcc] with v hv
    exact D.U_envelope v hv
  have hEnvInt :
      (∫ v, (D.U v - D.U D.a1) ∂D.mu) =
        ∫ v, (∫ t in D.a1..v, D.Q t) ∂D.mu :=
    integral_congr_ae hEnvAE

  let κ : ℝ → ℝ := fun t => max D.a1 (min D.b1 t)
  have hκ_mem (t : ℝ) : κ t ∈ Set.Icc D.a1 D.b1 := by
    constructor
    · exact le_max_left _ _
    · exact max_le D.h1.le (min_le_left _ _)
  have hκ_eq (t : ℝ) (ht : t ∈ Set.Icc D.a1 D.b1) : κ t = t := by
    simp [κ, min_eq_right ht.2, max_eq_right ht.1]
  let Qe : ℝ → ℝ := fun t => D.Q (κ t)
  have hQe_mono : Monotone Qe := by
    intro x y hxy
    exact D.Q_mono (hκ_mem x) (hκ_mem y) (max_le_max le_rfl (min_le_min_left _ hxy))
  have hQe_meas : Measurable Qe := hQe_mono.measurable
  have hQe_range (t : ℝ) : Qe t ∈ Set.Icc 0 1 := by
    exact ⟨D.Q_nonneg (κ t) (hκ_mem t), D.Q_le_one (κ t) (hκ_mem t)⟩
  let F : ℝ × ℝ → ℝ := fun p => if p.1 ≤ p.2 then Qe p.1 else 0
  have hFmeas : Measurable F := by
    apply Measurable.ite (measurableSet_le measurable_fst measurable_snd)
    · exact hQe_meas.comp measurable_fst
    · exact measurable_const
  have hFrange : ∀ p : ℝ × ℝ, F p ∈ Set.Icc 0 1 := by
    intro p
    by_cases hp : p.1 ≤ p.2
    · simpa [F, hp] using hQe_range p.1
    · simp [F, hp]
  let μt : Measure ℝ := volume.restrict (Set.Icc D.a1 D.b1)
  let μv : Measure ℝ := D.mu.restrict (Set.Icc D.a1 D.b1)
  have hFint : Integrable F (μt.prod μv) := by
    have hmem : MemLp F 1 (μt.prod μv) :=
      memLp_of_bounded (Filter.Eventually.of_forall hFrange) hFmeas.aestronglyMeasurable 1
    exact hmem.integrable (by norm_num)
  have hInner (v : ℝ) (hv : v ∈ Set.Icc D.a1 D.b1) :
      (∫ t in D.a1..v, D.Q t) = ∫ t, F (t, v) ∂μt := by
    rw [intervalIntegral.integral_of_le hv.1]
    change (∫ t in Set.Ioc D.a1 v, D.Q t ∂volume) =
      ∫ t in Set.Icc D.a1 D.b1, F (t, v) ∂volume
    rw [← integral_indicator measurableSet_Ioc, ← integral_indicator measurableSet_Icc]
    apply integral_congr_ae
    filter_upwards [(Set.countable_singleton D.a1).ae_notMem volume] with t hta
    by_cases ht : t ∈ Set.Icc D.a1 D.b1
    · have hta' : D.a1 ≠ t := by
        intro h
        apply hta
        simp [h]
      by_cases htv : t ≤ v
      · have htIoc : t ∈ Set.Ioc D.a1 v :=
          ⟨lt_of_le_of_ne ht.1 hta', htv⟩
        have hQe : Qe t = D.Q t := by dsimp [Qe]; rw [hκ_eq t ht]
        simp [Set.indicator, ht, htIoc, F, htv, hQe]
      · have htIoc : t ∉ Set.Ioc D.a1 v := by
          intro ht'
          exact htv ht'.2
        simp [Set.indicator, ht, htIoc, F, htv]
    · have htIoc : t ∉ Set.Ioc D.a1 v := by
        intro ht'
        exact ht ⟨ht'.1.le, le_trans ht'.2 hv.2⟩
      simp [Set.indicator, ht, htIoc, F]
  have hOuter :
      (∫ v, (∫ t in D.a1..v, D.Q t) ∂D.mu) =
        ∫ v, (∫ t, F (t, v) ∂μt) ∂D.mu := by
    apply integral_congr_ae
    filter_upwards [hμIcc] with v hv
    exact hInner v hv
  have hFint' : Integrable (Function.uncurry (fun t v => F (t, v))) (μt.prod μv) := by
    convert hFint using 1
    funext p
    cases p
    rfl
  have hSwap := (integral_integral_swap
    (f := fun t v => F (t, v)) hFint').symm
  have hSwap' :
      (∫ v, (∫ t, F (t, v) ∂μt) ∂D.mu) =
        ∫ t, (∫ v, F (t, v) ∂D.mu) ∂μt := by
    simpa [μt, μv, hμrestrict] using hSwap
  have hTail (t : ℝ) :
      (∫ v, F (t, v) ∂D.mu) = Qe t * D.mu.real {v | t ≤ v} := by
    have hEq : (fun v => F (t, v)) =
        (Set.Ici t).indicator (fun _ => Qe t) := by
      funext v
      simp [F, Set.indicator, Set.mem_Ici]
    rw [hEq, integral_indicator_const (Qe t) measurableSet_Ici]
    simp [Set.Ici, smul_eq_mul, mul_comm]
  have hTailInt :
      (∫ t, (∫ v, F (t, v) ∂D.mu) ∂μt) =
        ∫ t, Qe t * D.mu.real {v | t ≤ v} ∂μt := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall hTail
  have hReplaceQ :
      (∫ t, Qe t * D.mu.real {v | t ≤ v} ∂μt) =
        ∫ t, D.Q t * D.mu.real {v | t ≤ v} ∂μt := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    have hQe : Qe t = D.Q t := by dsimp [Qe]; rw [hκ_eq t ht]
    simp [hQe]
  have hInterval :
      (∫ t, D.Q t * D.mu.real {v | t ≤ v} ∂μt) =
        ∫ t in D.a1..D.b1, D.Q t * D.mu.real {v | t ≤ v} := by
    change (∫ t in Set.Icc D.a1 D.b1, D.Q t * D.mu.real {v | t ≤ v} ∂volume) = _
    rw [intervalIntegral.integral_of_le D.h1.le]
    rw [← integral_indicator measurableSet_Icc, ← integral_indicator measurableSet_Ioc]
    apply integral_congr_ae
    filter_upwards [(Set.countable_singleton D.a1).ae_notMem volume] with t hta
    by_cases ht : t ∈ Set.Icc D.a1 D.b1
    · have hta' : D.a1 ≠ t := by
        intro h
        apply hta
        simp [h]
      have htIoc : t ∈ Set.Ioc D.a1 D.b1 := ⟨lt_of_le_of_ne ht.1 hta', ht.2⟩
      simp [Set.indicator, ht, htIoc]
    · have htIoc : t ∉ Set.Ioc D.a1 D.b1 := by
        intro ht'
        exact ht ⟨ht'.1.le, ht'.2⟩
      simp [Set.indicator, ht, htIoc]
  calc
    (∫ v, D.U v ∂D.mu) = D.U D.a1 + ∫ v, (D.U v - D.U D.a1) ∂D.mu := hdecomp
    _ = D.U D.a1 + ∫ v, (∫ t in D.a1..v, D.Q t) ∂D.mu := by rw [hEnvInt]
    _ = D.U D.a1 + ∫ t in D.a1..D.b1, D.Q t * D.mu.real {v | t ≤ v} := by
      rw [hOuter, hSwap', hTailInt, hReplaceQ, hInterval]

theorem EW_eq (D : MSData) :
    (∫ c, D.W c ∂D.nu) = D.W D.b2 +
      ∫ t in D.a2..D.b2, D.R t * D.nu.real {c | c ≤ t} := by
  letI : IsProbabilityMeasure D.nu := D.nu_probability
  have hfullLip : LipschitzOnWith 1 D.W (Set.Icc D.a2 D.b2) :=
    LipschitzOnWith.mk_one fun c hc c' hc' => by
      simpa [Real.dist_eq] using D.W_lip c hc c' hc'
  have hWcont : ContinuousOn D.W (Set.Icc D.a2 D.b2) := hfullLip.continuousOn
  have hνIcc : ∀ᵐ c ∂D.nu, c ∈ Set.Icc D.a2 D.b2 := by
    filter_upwards [D.nu.support_mem_ae] with c hc
    exact D.nu_supported hc
  have hνrestrict : D.nu.restrict (Set.Icc D.a2 D.b2) = D.nu :=
    Measure.restrict_eq_self_of_ae_mem hνIcc
  have hWon : IntegrableOn D.W (Set.Icc D.a2 D.b2) D.nu :=
    hWcont.integrableOn_of_subset_isCompact isCompact_Icc measurableSet_Icc
      (by intro x hx; exact hx) (measure_ne_top D.nu (Set.Icc D.a2 D.b2))
  have hWint : Integrable D.W D.nu := by
    rw [← hνrestrict]
    exact hWon
  have hconst : ∫ _ : ℝ, D.W D.b2 ∂D.nu = D.W D.b2 := by simp
  have hdecomp : (∫ c, D.W c ∂D.nu) = D.W D.b2 +
      ∫ c, (D.W c - D.W D.b2) ∂D.nu := by
    rw [integral_sub hWint (integrable_const _), hconst]
    ring
  have hEnvAE : ∀ᵐ c ∂D.nu, D.W c - D.W D.b2 = ∫ t in c..D.b2, D.R t := by
    filter_upwards [hνIcc] with c hc
    exact D.W_envelope c hc
  have hEnvInt :
      (∫ c, (D.W c - D.W D.b2) ∂D.nu) =
        ∫ c, (∫ t in c..D.b2, D.R t) ∂D.nu :=
    integral_congr_ae hEnvAE

  let κ : ℝ → ℝ := fun t => max D.a2 (min D.b2 t)
  have hκ_mem (t : ℝ) : κ t ∈ Set.Icc D.a2 D.b2 := by
    constructor
    · exact le_max_left _ _
    · exact max_le D.h2.le (min_le_left _ _)
  have hκ_eq (t : ℝ) (ht : t ∈ Set.Icc D.a2 D.b2) : κ t = t := by
    simp [κ, min_eq_right ht.2, max_eq_right ht.1]
  let Re : ℝ → ℝ := fun t => D.R (κ t)
  have hRe_anti : Antitone Re := by
    intro x y hxy
    exact D.R_anti (hκ_mem x) (hκ_mem y)
      (max_le_max le_rfl (min_le_min_left _ hxy))
  have hRe_meas : Measurable Re := hRe_anti.measurable
  have hRe_range (t : ℝ) : Re t ∈ Set.Icc 0 1 := by
    exact ⟨D.R_nonneg (κ t) (hκ_mem t), D.R_le_one (κ t) (hκ_mem t)⟩
  let F : ℝ × ℝ → ℝ := fun p => if p.2 ≤ p.1 then Re p.1 else 0
  have hFmeas : Measurable F := by
    apply Measurable.ite (measurableSet_le measurable_snd measurable_fst)
    · exact hRe_meas.comp measurable_fst
    · exact measurable_const
  have hFrange : ∀ p : ℝ × ℝ, F p ∈ Set.Icc 0 1 := by
    intro p
    by_cases hp : p.2 ≤ p.1
    · simpa [F, hp] using hRe_range p.1
    · simp [F, hp]
  let μt : Measure ℝ := volume.restrict (Set.Icc D.a2 D.b2)
  let μc : Measure ℝ := D.nu.restrict (Set.Icc D.a2 D.b2)
  have hFint : Integrable F (μt.prod μc) := by
    have hmem : MemLp F 1 (μt.prod μc) :=
      memLp_of_bounded (Filter.Eventually.of_forall hFrange) hFmeas.aestronglyMeasurable 1
    exact hmem.integrable (by norm_num)
  have hInner (c : ℝ) (hc : c ∈ Set.Icc D.a2 D.b2) :
      (∫ t in c..D.b2, D.R t) = ∫ t, F (t, c) ∂μt := by
    rw [intervalIntegral.integral_of_le hc.2]
    change (∫ t in Set.Ioc c D.b2, D.R t ∂volume) =
      ∫ t in Set.Icc D.a2 D.b2, F (t, c) ∂volume
    rw [← integral_indicator measurableSet_Ioc, ← integral_indicator measurableSet_Icc]
    apply integral_congr_ae
    filter_upwards [(Set.countable_singleton c).ae_notMem volume] with t htc
    by_cases ht : t ∈ Set.Icc D.a2 D.b2
    · have htc' : c ≠ t := by
        intro h
        apply htc
        simp [h]
      by_cases hct : c ≤ t
      · have htIoc : t ∈ Set.Ioc c D.b2 := ⟨lt_of_le_of_ne hct htc', ht.2⟩
        have hRe : Re t = D.R t := by dsimp [Re]; rw [hκ_eq t ht]
        simp [Set.indicator, ht, htIoc, F, hct, hRe]
      · have htIoc : t ∉ Set.Ioc c D.b2 := by
          intro ht'
          exact hct ht'.1.le
        simp [Set.indicator, ht, htIoc, F, hct]
    · have htIoc : t ∉ Set.Ioc c D.b2 := by
        intro ht'
        exact ht ⟨le_trans hc.1 ht'.1.le, ht'.2⟩
      simp [Set.indicator, ht, htIoc, F]
  have hOuter :
      (∫ c, (∫ t in c..D.b2, D.R t) ∂D.nu) =
        ∫ c, (∫ t, F (t, c) ∂μt) ∂D.nu := by
    apply integral_congr_ae
    filter_upwards [hνIcc] with c hc
    exact hInner c hc
  have hFint' : Integrable (Function.uncurry (fun t c => F (t, c))) (μt.prod μc) := by
    convert hFint using 1
    funext p
    cases p
    rfl
  have hSwap := (integral_integral_swap
    (f := fun t c => F (t, c)) hFint').symm
  have hSwap' :
      (∫ c, (∫ t, F (t, c) ∂μt) ∂D.nu) =
        ∫ t, (∫ c, F (t, c) ∂D.nu) ∂μt := by
    simpa [μt, μc, hνrestrict] using hSwap
  have hTail (t : ℝ) :
      (∫ c, F (t, c) ∂D.nu) = Re t * D.nu.real {c | c ≤ t} := by
    have hEq : (fun c => F (t, c)) =
        (Set.Iic t).indicator (fun _ => Re t) := by
      funext c
      simp [F, Set.indicator, Set.mem_Iic]
    rw [hEq, integral_indicator_const (Re t) measurableSet_Iic]
    simp [Set.Iic, smul_eq_mul, mul_comm]
  have hTailInt :
      (∫ t, (∫ c, F (t, c) ∂D.nu) ∂μt) =
        ∫ t, Re t * D.nu.real {c | c ≤ t} ∂μt := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall hTail
  have hReplaceR :
      (∫ t, Re t * D.nu.real {c | c ≤ t} ∂μt) =
        ∫ t, D.R t * D.nu.real {c | c ≤ t} ∂μt := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    have hRe : Re t = D.R t := by dsimp [Re]; rw [hκ_eq t ht]
    simp [hRe]
  have hInterval :
      (∫ t, D.R t * D.nu.real {c | c ≤ t} ∂μt) =
        ∫ t in D.a2..D.b2, D.R t * D.nu.real {c | c ≤ t} := by
    change (∫ t in Set.Icc D.a2 D.b2, D.R t * D.nu.real {c | c ≤ t} ∂volume) = _
    rw [intervalIntegral.integral_of_le D.h2.le]
    rw [← integral_indicator measurableSet_Icc, ← integral_indicator measurableSet_Ioc]
    apply integral_congr_ae
    filter_upwards [(Set.countable_singleton D.a2).ae_notMem volume] with t hta
    by_cases ht : t ∈ Set.Icc D.a2 D.b2
    · have hta' : D.a2 ≠ t := by
        intro h
        apply hta
        simp [h]
      have htIoc : t ∈ Set.Ioc D.a2 D.b2 := ⟨lt_of_le_of_ne ht.1 hta', ht.2⟩
      simp [Set.indicator, ht, htIoc]
    · have htIoc : t ∉ Set.Ioc D.a2 D.b2 := by
        intro ht'
        exact ht ⟨ht'.1.le, ht'.2⟩
      simp [Set.indicator, ht, htIoc]
  calc
    (∫ c, D.W c ∂D.nu) = D.W D.b2 + ∫ c, (D.W c - D.W D.b2) ∂D.nu := hdecomp
    _ = D.W D.b2 + ∫ c, (∫ t in c..D.b2, D.R t) ∂D.nu := by rw [hEnvInt]
    _ = D.W D.b2 + ∫ t in D.a2..D.b2, D.R t * D.nu.real {c | c ≤ t} := by
      rw [hOuter, hSwap', hTailInt, hReplaceR, hInterval]

end MSData
