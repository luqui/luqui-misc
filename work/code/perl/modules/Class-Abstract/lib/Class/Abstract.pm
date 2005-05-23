package Class::Abstract;

use 5.006001;
use strict;
no warnings;  # Yeah, I know, bad form, yada yada yada.  I just don't like being bugged.

use Bit::Vector::Overload;
use Regexp::Common;
use Carp;

our $VERSION = '0.01';

our %TAGS;
our %METHODS;
our @CONVERT;


sub import {
    my ($pkg, %args) = @_;

    if ($args{-define}) {
        push @CONVERT, @{$args{-define}};
    }
    else {
        push @CONVERT, scalar caller;
    }

    for my $methname (keys %args) {
        next if $methname eq '-define';
        if ($methname =~ /^-/) {
            croak "No such option '$methname'";
        }
        if ($methname !~ /^ \w+ $/x) {
            croak "Garbage method name '$methname'";
        }

        my $meth = $METHODS{$methname};
        unless ($meth) {
            $meth = Class::Abstract::Method->new($methname, @{$args{$methname}}-1);
        }
        $meth->add_variant(@{$args{$methname}});
    }
}

sub new_tag_from_package {
    my ($class) = @_;
    no strict 'refs';
    
    my $pkg = "$class\::";
    return if $TAGS{$class};

    for (@$pkg{ISA}) {
        new_tag_from_package($_);
    }
    Class::Abstract::Tag->new($class, @$pkg{ISA});
} 

sub convert_package {
    my ($class) = @_;
    no strict 'refs';

    my $pkg = "$class\::";
    my %converted;
    
    new_tag_from_package($class);
    
    for my $methname (keys %$pkg) {
        if (*{$$pkg{$methname}}{CODE}) {
            my $meth = $METHODS{$methname};
            unless ($meth) {
                $meth = Class::Abstract::Method->new($methname, 1);
            }
            $meth->add_variant($class, *{$$pkg{$methname}}{CODE});
            $converted{$methname}++;
        }
    }

    unless ($converted{new}) {
        my $meth = $METHODS{new};
        unless ($meth) {
            $meth = Class::Abstract::Method->new('new', 1);
        }
        $meth->add_variant($class, sub {
            my $self = Class::Abstract::Object->new($class);
            # XXX need to call BUILD
            $self;
        });
    }
}


# standard tags
Class::Abstract::Tag->new('Object');  
  Class::Abstract::Tag->new('Str', 'Object');
    Class::Abstract::Tag->new('Num', 'Str');
      Class::Abstract::Tag->new('Int', 'Num');
  Class::Abstract::Tag->new('Ref', 'Object');
    Class::Abstract::Tag->new('ScalarRef', 'Ref');
    Class::Abstract::Tag->new('Array', 'Ref');
    Class::Abstract::Tag->new('Hash', 'Ref');
    Class::Abstract::Tag->new('Code', 'Ref');
    Class::Abstract::Tag->new('Glob', 'Ref');

our %REFTAG = (
    SCALAR => 'ScalarRef',
    ARRAY  => 'Array',
    HASH   => 'Hash',
    CODE   => 'Code',
    REF    => 'ScalarRef',
    GLOB   => 'Glob',
);

sub get_tag {
    my ($val) = @_;
    if (ref $val eq 'Class::Abstract::Object') {
        $val->Class::Abstract::Object::Meta::get_tags;
    }
    else {
        scalar_tag($val);
    }
}

sub scalar_tag {
    my ($val) = @_;
    if (ref $val) {
        $REFTAG{ref $val} || ref $val;
    }
    else {
        if ($val =~ /^ $Regexp::Common::RE{num}{int} $/ox) {
            ('Int')
        }
        elsif ($val =~ /^ $Regexp::Common::RE{num}{real} $/ox) {
            ('Num')
        }
        elsif (exists $TAGS{$val}) {  # if it's an existing class
            ('Str', $val)
        }
        else {
            ('Str')
        }
    }
}

package Class::Abstract::Tag;

use Carp;

sub new {
    my ($class, $name, @parents) = @_;

    for (@parents) {
        unless ($Class::Abstract::TAGS{$_}) {
            croak "No such tag '$_' to use as parent when creating new tag '$name'";
        }
    }

    my $self = bless {
        name      => $name,
        parents   => { map { $_ => 1 } @parents },
        ancestors => { $name => 1,
                       map { 
                        $_ => 1, 
                        $Class::Abstract::TAGS{$_}->ancestor_map,
                       } @parents 
                     },

        # an entry in mmtable looks like:
        #   method_name => {
        #       rev => "aduvb",  # revision string for cache checking
        #       bits => [
        #           0b10110100,  # bitfield for arg 1
        #           0b01110011,  # bitfield for arg 2
        #           ...
        #       ],
        #   }
        mmtable   => { },
    } => ref $class || $class;

    $Class::Abstract::TAGS{$name} = $self;
}

sub name {
    my ($self) = @_;
    $self->{name};
}

sub parents {
    my ($self) = @_;
    keys %{$self->{parents}};
}

sub ancestors {
    my ($self) = @_;
    keys %{$self->{ancestors}};
}

sub ancestor_map {
    my ($self) = @_;
    %{$self->{ancestors}};
}

sub is_ancestor {
    my ($self, $anc) = @_;
    $anc = $anc->{name} if ref $anc;
    $self->{ancestors}{$anc};
}

sub refresh_mmtable {
    my ($self, $name) = @_;
    my $meth = $Class::Abstract::METHODS{$name};
    if ($self->{mmtable}{$name}{rev} ge $meth->revision) {  # greater? whatever
        $self->{mmtable}{$name}{bits};
    }
    else {
        $self->{mmtable}{$name}{bits} = $meth->make_bits($self);
    }
}

sub get_bits {
    my ($self, $meth, $arg) = @_;
    $self->refresh_mmtable($meth)->[$arg];
}


package Class::Abstract::Method;

use Carp;

sub new {
    my ($class, $name, $params) = @_;
    
    my $self = bless {
        name => $name,
        variants => [ ],
        params => $params,
        ordering => undef,
        rev => "a",
    } => ref $class || $class;

    $Class::Abstract::METHODS{$name} = $self;
}

sub add_variant {
    my $self = shift;
    my $code = pop;
    my @params = @_;

    for (@params) {
        $_ = [ $_ ] unless ref $_;
        for (@$_) {
            unless (exists $Class::Abstract::TAGS{$_}) {
                croak "No such tag '$_'";
            }
        }
    }
    
    push @{$self->{variants}}, {
        params => [ @params ],
        code => $code,
        validate => undef,
    };

    $self->refresh_ordering;

    ++$self->{rev}; 
}

sub revision {
    my ($self) = @_;
    $self->{rev};
}

sub make_bits {
    my ($self, $tag) = @_;

    unless (ref $tag) {
        $tag = $Class::Abstract::TAGS{$tag} or croak "no such tag '$tag'";
    }

    my @ret;

    for my $param (0..$self->{params}-1) {
        $ret[$param] = Bit::Vector->new(scalar @{$self->{variants}});

        VARIANT:
        for my $var (0..@{$self->{variants}}-1) {
            for (@{$self->{variants}[$var]{params}[$param]}) {
                if ($tag->is_ancestor($_)) {
                    $ret[$param]->Bit_On($var);
                    next VARIANT;
                }
            }
        }
    }

    return \@ret;
}

sub refresh_ordering {
    my ($self) = @_;

    my %graph;
    for my $a (0..@{$self->{variants}}-1) {
        for my $b (0..@{$self->{variants}}-1) {
            if ($self->variant_includes($a, $b)) {
                push @{$graph{$b}}, $a;
            }
        }
    }

    for (@{$self->{variants}}) {
        my $v = Bit::Vector->new(scalar @{$self->{variants}});
        $v->Fill;
        $_->{validate} = $v;
    }

    my @neworder;
    my $seen = {};
    for (0..@{$self->{variants}}-1) {
        $self->dfs_traverse($_, \%graph, \@neworder, $seen);
    }

    my @neworderinv;
    @neworderinv[@neworder] = 0..$#neworder;

    # now reorder everything
    @{$self->{variants}} = @{$self->{variants}}[@neworder];
    for my $variant (@{$self->{variants}}) {
        my @index = $variant->{validate}->Index_List_Read;
        for (@index) {
            $_ = $neworderinv[$_];
        }
        $variant->{validate}->Empty;
        $variant->{validate}->Index_List_Store(@index);
    }
}

sub dfs_traverse {
    my ($self, $vertex, $graph, $list, $seen) = @_;
    return if $seen->{$vertex}++;

    for (@{$graph->{$vertex}}) {
        $self->dfs_traverse($_, $graph, $list, $seen);
        $self->{variants}[$vertex]{validate} &= 
            $self->{variants}[$_]{validate} &~
                Bit::Vector->new_Enum(scalar @{$self->{variants}}, $_);
    }
    
    unshift @$list, $vertex;
}

sub variant_includes {
    my ($self, $vA, $vB) = @_;

    my $better;
    for my $param (0..$self->{params}-1) {
        TAG:
        for my $tagname (@{$self->{variants}[$vB]{params}[$param]}) {
            my $tag = $Class::Abstract::TAGS{$tagname};
            for my $tagname2 (@{$self->{variants}[$vA]{params}[$param]}) {
                if ($tag->is_ancestor($tagname2)) {
                    $better = 1 if $tagname ne $tagname2;
                    next TAG;
                }
            }
            return;
        }
    }

    return $better;
}

# map a list of tagsets into a set of variants
sub find_variants {
    my ($self, $disambig, @inv) = @_;

    if (@inv < $self->{params}) {
        croak "Not enough invocants given; expecting $self->{params}";
    }
    if (@inv > $self->{params}) {
        croak "Too many invocants given; expecting $self->{params}";
    }

    
    my $bits = Bit::Vector->new(scalar @{$self->{variants}});
    $bits->Fill;
    for my $param (0..$#inv) {
        my $tagbits = $bits->Shadow;
        for my $tag (@{$inv[$param]}) {
            unless (ref $tag) {
                $tag = $Class::Abstract::TAGS{$tag} 
                    or croak "No such tag $tag";
            }
            $tagbits |= $tag->get_bits($self->{name}, $param);
        }
        $bits &= $tagbits;
    }

    my $valid = Bit::Vector->new(scalar @{$self->{variants}});
    $valid->Fill;

    my @ind = $bits->Index_List_Read;
    return @ind unless $disambig;
    
    my @ret;

    VARIANT:
    for my $var (@ind) {
        if ($valid->bit_test($var)) {
            push @ret, $var;
            $valid &= $self->{variants}[$var]{validate};
        }
    }
    @ret;
}

sub variant_sig {
    my ($self, $var) = @_;
    $self->{name} . '(' . 
            join(', ', map { join(' | ', @$_) } @{$self->{variants}[$var]{params}}) 
        . ')';
}

sub call {
    my $self = shift;
    my @tags = map { [ Class::Abstract::get_tag($_) ] } @_[0..$self->{params}-1];

    my @var = $self->find_variants(1, @tags);  # 1 is for d1sambiguate

    if (@var == 1) {
        goto &{$self->{variants}[$var[0]]{code}};
    }
    elsif (@var == 0) {
        croak "No applicable variant found for '$self->{name}':\n"
            . "  Arguments: " . join(', ', map { join(' & ', map { $_->name } @$_) } @tags) . "\n";
    }
    else {
        my $msg = "Ambiguous method call of '$self->{name}':\n";
        $msg .= "  Arguments: " . join(', ', map { join(' & ', map { $_->name } @$_) } @tags) . "\n";
        $msg .= "  Matching variants:\n";
        for (@var) {
            $msg .= "    " . $self->variant_sig($_) . "\n";
        }
        croak $msg;
    }
}

sub call_all_child_first {
    my $self = shift;
    my @tags = map { [ Class::Abstract::get_tag($_) ] } @_[0..$self->{params}-1];

    my @var = $self->find_variants(0, @tags);  # 0 is for d0n't disambiguate

    for (@var) {
        $self->{variants}[$_]{code}->(@_);
    }
}

sub call_all_parent_first {
    my $self = shift;
    my @tags = map { [ Class::Abstract::get_tag($_) ] } @_[0..$self->{params}-1];

    my @var = reverse $self->find_variants(0, @tags);  # 0 is for d0n't disambiguate

    for (@var) {
        $self->{variants}[$_]{code}->(@_);
    }
}

package Class::Abstract::Object;

sub AUTOLOAD {
    our $AUTOLOAD =~ s/.*:://;
    unshift @_, $Class::Abstract::METHODS{$AUTOLOAD} 
        || $AUTOLOAD eq 'DESTROY' && return
        || Carp::croak("No method found of name '$AUTOLOAD'");
    goto &Class::Abstract::Method::call;
}

package Class::Abstract::Object::Meta;

sub new {
    my ($class, @init_tags) = @_;
    
    my $self = bless { } => 'Class::Abstract::Object';

    $self->{'*tags'} = { map { $_ => 1 } @init_tags };

    factor_tags($self);
    $self;
}

sub factor_tags {
    my ($self, @tags) = @_;

    my %kill;
    for my $src (@tags) {
        for my $dest (keys %{$self->{'*tags'}}) {
            if ($src ne $dest && $src->is_ancestor($dest)) {
                $kill{$dest} = 1;
            }
        }
    }

    delete @{$self->{'*tags'}}{keys %kill};
}

sub get_tags {
    my ($self) = @_;
    keys %{$self->{'*tags'}};
}

1;
