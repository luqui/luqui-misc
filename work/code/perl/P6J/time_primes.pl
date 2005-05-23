#! /bin/csh 

foreach file ( prime* ) 
	echo -n "	${file}: "
	time $file > /dev/null
end
