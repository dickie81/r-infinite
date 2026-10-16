import ShellSixth
import BohrLandau

/-! Stack review 3: round 402's `w > 0` theorems give round 401's `w > 1/6` and `w > 1/4` ones. -/

example : type_of% @ShellSixth.tendsto_NX_div_sixth := by
  intro w hw; exact BohrLandau.tendsto_NX_div_pos (by linarith)
example : type_of% @ShellDensity.tendsto_NX_div_quarter := by
  intro w hw; exact BohrLandau.tendsto_NX_div_pos (by linarith)
example : type_of% @ShellSixth.tendsto_outside_div_sixth := by
  intro w hw F hF; exact BohrLandau.tendsto_outside_div_pos (by linarith) hF
example : type_of% @ShellDensity.tendsto_outside_div_quarter := by
  intro w hw F hF; exact BohrLandau.tendsto_outside_div_pos (by linarith) hF
