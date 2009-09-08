my $output = 0;
my $PPCHOME = "";
my $WHYHOME = "";

while ( <> ) {
    if ($_ =~ /PPCHOME: (.*)/) {
        $PPCHOME=$1;
        $output=0
    }
    if ($_ =~ /WHYHOME: (.*)/) {
        $WHYHOME=$1;
        $output=0
    }

    if ( $_ =~ /total wallclock time/ ) {
	$output = 0;
    }
    if ( $_ =~ /End (.*) for diff/ ) {
	$output = 0;
    }
    if ( $output == 1) {
        s|${PPCHOME}|PPCHOME|g;
        s|${WHYHOME}|WHYHOME|g;
	print $_;
    }
    if ( $_ =~ /Running (.*) on proof obligations/ ) {
	$output = 1;
    }
    if ( $_ =~ /Begin (.*) for diff/ ) {
	$output = 1;
    }
}
