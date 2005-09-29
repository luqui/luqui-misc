package Language::AttributeGrammar::VisitOrder;

=pod

C<make_visit_order> takes a data structure like this:

    {
      "nonterminal" => [ {
          target => {
            attribute => "some_attribute",
            node      => ("some_child" or "SELF"),
            type      => "child_nonterminal",
          },
          deps        => [ {
            attribute => "another_attribute",
            node      => ("another_child" or "SELF"),
            type      => "another_child_nonterminal",
          }, ... ],
          # other entries in this hash are preserved
        }, 
        ...
      ],
      ...
    }

and returns a structure like this:

  {
    "nonterminal" => [ ACTION1, ACTION2, ... ],
    ...
  }

where each action is either:

  { type => "compute",
    rule => { 
      # one of the target-deps hashes above
    } }

or:

  { type => "visit",
    node => "somechild",
    entry => (1 or 2 or ...) }

or:

  { type => "leave",
    exit => (1 or 2 or ...) }

=cut
