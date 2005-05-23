package Perl6::Junctions;
our $VERSION = '0.01';
use Carp;
use Scalar::Util qw(reftype looks_like_number);
use overload

=for later
	'${}' => sub { @{$_[0]}==1 ? ${$_[0][0]}
			           : bless [map {$$_} @{$_[0]}], ref $_[0] },
	'@{}' => sub { croak "Can't access multi-valued junction as array" 
			unless @{$_[0]}==1 && reftype $_[0][0] eq 'ARRAY';
		       $_[0][0] },
	'%{}' => sub { croak "Can't access multi-valued junction as hash" 
			unless @{$_[0]}==1 && reftype $_[0][0] eq 'HASH';
		       $_[0][0] },
=cut

	'*{}' => sub { croak "Can't access multi-valued junction as typeglob" 
				unless @{$_[0]}==1;
		       my $rtype = reftype($_[0][0])||"";
		       return $_[0][0] if $rtype eq 'GLOB';
		       return \*{$_[0][0]} if !$rtype;
		       croak "Not a GLOB reference";
		     },
	'&{}' => sub { my $junction = $_[0];
		       sub { bless [map &$_, @$junction], ref $junction }
		     },
;

sub import {
	*{caller()."::$_"} = \&$_ for qw( any all one none );
	shift;
	my @overloads = grep /^[^-]/, @_;
	# use Data::Dumper 'Dumper';
	# print Dumper [ map { s/^CORE/CORE::GLOBAL/; $_ }
			   # map "$_(".prototype($_).")", @overloads ];

	if (grep /-operators/, @_) {
		'overload'->import(
			'|'     => sub { croak "Junctive | not defined" },
			'&'     => sub { croak "Junctive & not defined" },
			'^'     => sub { croak "Junctive ^ not defined" },
		);
	}
	else {
		overload::constant(
			integer => sub { print "Makeymakey\n"; any($_[1]) },
			float   => sub { any($_[1]) },
			binary  => sub { any($_[1]) },
			q       => sub { any($_[1]) },
		);
		'overload'->import(
			'|'     => sub { any(@_[0,1]) },
			'&'     => sub { all(@_[0,1]) },
			'^'     => sub { one(@_[0,1]) },
		);
		package Perl6::Junctions::ANY;
		'overload'->import(
		    '|' => sub { $_[2] ? Perl6::Junctions::any($_[1],@{$_[0]})
				       : Perl6::Junctions::any(@{$_[0]},$_[1]) }
		);
		package Perl6::Junctions::ALL;
		'overload'->import(
		    '&' => sub { $_[2] ? Perl6::Junctions::all($_[1],@{$_[0]})
				       : Perl6::Junctions::all(@{$_[0]},$_[1]) }
		);
		package Perl6::Junctions::ONE;
		'overload'->import(
		    '^' => sub { $_[2] ? Perl6::Junctions::one($_[1],@{$_[0]})
				       : Perl6::Junctions::one(@{$_[0]},$_[1]) }
		);
	}
}

for my $name (qw/ all any one none /) {
	eval qq{ sub $name { bless [\@_], 'Perl6::Junctions::\U$name\E' } }
}

my %prec = (
	""                       => 0,
	'Perl6::Junctions::ANY'  => 1,
	'Perl6::Junctions::ONE'  => 2,
	'Perl6::Junctions::NONE' => 3,
	'Perl6::Junctions::ALL'  => 4,
);

sub ___s_et__ {
	my ($x,$y,$rev) = @_;
	($x,$y)=($y,$x) if $rev;
	my ($refx, $refy) = (ref($x)||"", ref($y)||"");
	return ($x, $y), ($prec{$refx} > $prec{$refy} ? ($refx,1) : ($refy,0));
}

sub ___d_ist__ {
	my ($x, $y, $yoverx) = @_;
	if ($yoverx) { return map [$_, $y], @$x }
	else	     { return map [$x, $_], @$y }
}

use overload
	'""'	 => sub { return $_[0][0] if $_[0]->values == 1;
                      croak "Can't stringify a junction. Use 'dump' method";
                    },
	'neg'	 => sub { bless [map {-$_} @{$_[0]}], ref $_[0] },
	q{atan2} => sub { my ($x,$y,$rtype,$ridx) = ___s_et__(@_);
		          bless [map {atan2($_->[0],$_->[1])} ___d_ist__->($x,$y,$ridx)],
				$rtype;
		     },
;

my @unops = qw{ ! ~ cos sin exp log sqrt };

my $unop_template = q{
	q{%s} => sub { bless [map {%s($_)} @{$_[0]}], ref $_[0] },
};

my @binops =
	qw{ + - * / % ** << >> x . == != < > <= >= <=> eq ne lt gt le ge cmp };

my $binop_template = q{
	q{%s} => sub { my ($x,$y,$rtype,$ridx) = ___s_et__(@_);
		       bless [map {$_->[0] %s $_->[1]} ___d_ist__($x,$y,$ridx)],
			     $rtype;
		     },
};

eval "use overload "
   . join("", map { sprintf $binop_template, $_, $_ } @binops)
   . join("", map { sprintf $unop_template, $_, $_ } @unops)
;

# Handle method calls to junctive invocants...

sub DESTROY {}

sub AUTOLOAD {
	my $junction = shift;
    use Data::Dumper 'Dumper';
	my ($method) = $AUTOLOAD =~ m/.*::(.*)/;
	bless [map $_->$method(@_), @$junction], ref $junction;
}

# Utility methods

sub pick {
    my ($junct) = @_;
    return $junct->[rand @{$junct}]
}

sub _raw_values {
    my ($junct) = @_;
    my @values;
    for my $state (@$junct) {
        if (UNIVERSAL::isa($state, 'Perl6::Junctions')) {
            push @values, _raw_values($state);
        }
        else {
            push @values, $state;
        }
    }
    return @values;
}

sub values {
    my ($junct) = @_;
    my @values;
    for my $state (@$junct) {
        if (UNIVERSAL::isa($state, 'Perl6::Junctions')) {
            push @values, _raw_values($state);
        }
        else {
            push @values, $state;
        }
    }

    for my $val (@values) {
        undef $val
            unless looks_like_number($val) || ref($val) ? $val == $junct
                 :                                        $val eq $junct
                 ;
    }
    return grep { defined } @values;
}

sub states {
    my ($junct) = @_;
    return @$junct;
}

sub dump {
    my ($junct) = @_;
    return $junct->[0] if $junct->values == 1;
    my $vals = join ",", map { UNIVERSAL::isa($_,'Perl6::Junctions')
                                    ? $_->dump
                                    : $_
                             } @{$junct};
    my $type = ref $junct;
    $type =~ s/.*::(.*)/\L$1/;
    return "$type($vals)";
}


package Perl6::Junctions::ANY;
use base 'Perl6::Junctions';
use overload 'bool' => sub { for (@{$_[0]}) { return 1 if $_ } return "" };

package Perl6::Junctions::ALL;
use base 'Perl6::Junctions';
use overload 'bool' => sub { for (@{$_[0]}) { return "" unless $_ } return 1 };

package Perl6::Junctions::ONE;
use base 'Perl6::Junctions';
use overload
	'bool' => sub {
		my $matches=0;
		for (@{$_[0]}) { ++$matches if $_; return "" if $matches > 1 }
		return $matches==1;
	};

package Perl6::Junctions::NONE;
use base 'Perl6::Junctions';
use overload 'bool' => sub { for (@{$_[0]}) { return "" if $_ } return 1; };

1;
__END__
