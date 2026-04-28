$aux_dir = 'build';
$out_dir = '.';
$pdf_mode = 1;

# Treat undefined references and citations as build failures so the warnings
# surface as non-zero exit codes locally and in CI (xu-cheng/latex-action).
$warnings_as_errors = 1;

# Keep TeX log lines unwrapped so warning messages about long labels stay on
# one line. Without this, pdflatex wraps at column 79 and a warning like
# "Reference `rem:chirality-jacobian-separability' on page 1 undefined" can
# split the word "undefined" across two lines, defeating both latexmk's
# warnings_as_errors detection and the post-build regex scan.
$ENV{'max_print_line'} = 10000;
$ENV{'error_line'} = 254;
$ENV{'half_error_line'} = 238;

# pdflatex always writes <job>.synctex.gz next to the PDF (i.e. into $out_dir).
# Move it into $aux_dir after each compile so the source folder stays clean.
$success_cmd = 'internal move_synctex %R';
$failure_cmd = 'internal move_synctex %R';
$warning_cmd = 'internal move_synctex %R';

sub move_synctex {
    my $root = shift;
    my $src  = "$out_dir/$root.synctex.gz";
    my $dst  = "$aux_dir/$root.synctex.gz";
    if (-e $src) {
        rename $src, $dst;
    }
    return 0;
}

push @generated_exts, 'synctex.gz';
