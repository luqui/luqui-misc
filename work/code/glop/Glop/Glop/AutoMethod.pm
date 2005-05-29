package Glop::AutoMethod;

use strict;
use Carp;

our $AUTOLOAD;

sub import {
    my ($self, $meth) = @_;
    $meth || croak "Usage: use Glop::AutoMethod 'method_name'";
    my $package = caller;

    {
        no strict 'refs';
        *{"$package\::AUTOLOAD"} = sub {
            unless (eval "require $AUTOLOAD; 1") {
                $AUTOLOAD =~ /DESTROY/ ? return : confess "Method $AUTOLOAD not found: $@";
            }
            (my $name = $AUTOLOAD) =~ s/.*:://;
            my $code = $AUTOLOAD->can($meth);
            *$AUTOLOAD = sub { splice @_, 0, 1, "$package\::$name"; goto &$code };
            goto &$AUTOLOAD;
        };
    }       
}

1;
