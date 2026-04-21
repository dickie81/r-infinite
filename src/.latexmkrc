$aux_dir = 'build';
$out_dir = '.';
$pdf_mode = 1;

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
