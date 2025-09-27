#######################################################
# DC Shell Synthesis Flow
#######################################################

#------------------------------------------------------
# Setup search path and libraries
#------------------------------------------------------

set PERIOD 10
set DESIGN_NAME core
# set DESIGN_NAME fu_div
# set DESIGN_NAME fu_mul
# set DESIGN_NAME fu_lsu
set DESIGN_NAME fus

#TARGET_LIBRARY_FILES
set TLF [getenv TLF]
# set rtl_files [read_file ../synth.flist]
set fp [open "../synth.flist" r]
set rtl_files [split [read $fp] "\n"]
close $fp

puts $rtl_files

# gtech.db

# TODO add sdio
set_app_var target_library "$TLF"
set_app_var link_library   "* $TLF dw_foundation.sldb"

# TODO
# set_app_var link_library [list "* XXX XXXXsdio_ccs.db dw_foundation.sldb"]
# TODO add set_tlu_plus_files TLU ?
# TODO Multiple corners: After synthesis at nominal, 
# * check fast corner (lvt) for hold violations
# * slow corner (lvl) for setup violations

# TODO: add lvt

# create_clock_gating_cell

set_host_options -max_cores 8

# Eliminate tri-state nets and assign primitives in the output netlist
set_app_var verilogout_no_tri true

#------------------------------------------------------
#  Read, elaborate RTL
#------------------------------------------------------

# Create work dir
sh rm -rf work
sh mkdir work
define_design_lib dahulib -path work

# Build project

analyze -f sverilog -lib dahulib $rtl_files
# ../src/core/regfile.sv
# $rtl_files
elaborate ${DESIGN_NAME} -library dahulib

# Cells do not drive (LINT-1)
set_message_suppress LINT-1
# set_message_info -id LINT-1 -new_severity INFORMATION
# Unconnected ports (LINT-28)
set_message_suppress LINT-28
# set_message_info -id LINT-28 -new_severity INFORMATION

# check_design
report_message_info -all
get_lint_summary
report_lint -all

uniquify
link

check_design -summary

#------------------------------------------------------
#  Clock and timing constraints
#------------------------------------------------------

set clk_port clk
set clk_name clk
set clk_period 0.5; # 0.5 ns = 2 GHz

create_clock [get_ports $clk_port] -name $clk_name -period $clk_period

# Input / Output delays (external)
set_input_delay  0.05 -clock $clk_name [all_inputs];  # 50 ps
set_output_delay 0.05 -clock $clk_name [all_outputs]; # 50 ps

# Drive / Load assumptions
set_drive 0.05 [all_inputs]; # 50 fF drive
set_load 0.05 [all_outputs]; # 50 fF load

#------------------------------------------------------
# Compile / Synthesis
#------------------------------------------------------

# Disable retiming globally
set_dont_retime [get_cells -hierarchical *] true

get_designs *

# Enable retiming
foreach mod {fu_mul} {
    set d [get_designs $mod]
    if {[sizeof_collection $d] == 0} {
        puts "!! No design found for $mod"
        continue
    }

    set retimelist [get_cells -hierarchical -of_objects $d]
    # set retimelist [get_cells -hierarchical -filter "ref_name == $mod"]
    puts "Enable retiming for $mod: $retimelist"
    set_dont_retime $retimelist false
}

# if {[sizeof_collection $insts] > 0} {
#     puts ">> Enabling retiming for module '$mod' on [sizeof_collection $insts] instances"
#     set_dont_retime $insts false 
# } else {
#     puts "!! Warning: No instances found for module '$mod'"
# }

# -gate_clock TODO !
compile_ultra -no_boundary_optimization -retime
# 
report_qor -file qor_report.txt

#------------------------------------------------------
# Timing, Area, Power Reports
#------------------------------------------------------
report_timing -max_paths 20 -sort_by slack -delay_type max
report_area
report_power
report_qor

#------------------------------------------------------
# Write synthesized netlist
#------------------------------------------------------

# Report stats
# write -format verilog -hierarchy -output ${DCRM_FINAL_VERILOG_OUTPUT_FILE}
write -format verilog -hierarchy -output ${DESIGN_NAME}_synth.v
write -format ddc     -hierarchy -output ${DESIGN_NAME}_synth.ddc

# report_timing -nworst 10
# report_area -hier -nosplit
# write_sdc ${DESIGN_NAME}_synth.sdc
# write_sdf ${DESIGN_NAME}_synth.v.sdf

exit
