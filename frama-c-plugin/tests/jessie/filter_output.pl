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
        s|^make\[[0-9]+\]:|make:|g;
        s|jessie_[0-9]+|jessie_<somenum>|g;
        s|JC_[0-9]+|JC_<somenum>|g;
	print $_;
    }
    if ( $_ =~ /Running (.*) on proof obligations/ ) {
	$output = 1;
    }
    if ( $_ =~ /Begin (.*) for diff/ ) {
	$output = 1;
    }
}
