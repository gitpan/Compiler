C.pm needs to call saveoptree_callback($name, $root, $start) in two
places: (1) saving a CV, (2) saving PMOP repl code. The return value
needs to be a faked start op whose ppaddr is the compiled PP function.
That gets assigned to CvSTART or op_pmreplstart as appropriate.

saveoptree_callback needs to queue [$name, $root, $start, @padlist]
for saving which means that @padlist needs to be defined before
$cv->save is called.

