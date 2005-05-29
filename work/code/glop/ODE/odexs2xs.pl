#!/usr/bin/perl

sub check_keys {
    my ($name, $hash, @keys) = @_;
    for (@keys) {
        die "$name needs a $_ option" unless exists $hash->{$_};
    }
}

sub unindent {
    my ($level, $str) = @_;
    $str =~ s/^ {$level}//mg;
    $str;
}

our %TABLE = (
    dVAccessor => sub {
        my %opt = @_;
        check_keys 'dVAccessor', \%opt, 
            qw{name type set get};
        unindent 12, <<EOCODE;
            dV $opt{name}(inv, vec = NO_INIT)
                    $opt{type} inv;
                    dV vec;
                PREINIT:
                    dVector3 result;
                CODE:
                    if (items == 2) {
                        $opt{set}(inv, vec[0], vec[1], vec[2]);
                        RETVAL = vec;
                    }
                    else {
                        $opt{get}(inv, result);
                        RETVAL = result;
                    }
                OUTPUT:
                    RETVAL
EOCODE
    },
    dVRefAccessor => sub {
        my %opt = @_;
        check_keys 'dVRefAccessor', \%opt,
            qw{name type set get};
        unindent 12, <<EOCODE;
            dV $opt{name}(inv, vec = NO_INIT)
                    $opt{type} inv;
                    dV vec;
                CODE:
                    if (items == 2) {
                        $opt{set}(inv, vec[0], vec[1], vec[2]);
                        RETVAL = vec;
                    }
                    else {
                        RETVAL = (dV)$opt{get}(inv);
                    }
                OUTPUT:
                    RETVAL
EOCODE
    },
    auxAccessor => sub {
        my %opt = @_;
        check_keys 'auxAccessor', \%opt,
            qw{name type get set};
        unindent 12, <<EOCODE;
            void $opt{name}(inv, in = NO_INIT)
                    $opt{type} inv;
                    SV* in;
                PREINIT:
                    SV* pdata;
                PPCODE:
                    pdata = (SV*)$opt{get}(inv);
                    if (items == 2) {
                        if (pdata) SvREFCNT_dec(pdata);
                        if (in == &PL_sv_undef) {
                            $opt{set}(inv, NULL);
                        }
                        else {
                            SvREFCNT_inc(in);
                            $opt{set}(inv, in);
                        }
                        PUSHs(in);
                    }
                    else {
                        if (pdata) {
                            PUSHs(pdata);
                        }
                    }
EOCODE
    },
);

while (<>) {
    if (/^%%/) {
        my ($name, $pairs) = /^%% \s* (\w+) \s+ (.*?) \s* %% \s* $/x or next;
        my %opts = split /\s* (?: => | , ) \s*/x, $pairs;
        die "No such template $name" unless $TABLE{$name};
        $_ = $TABLE{$name}->(%opts);
    }
}
continue {
    print;
}
