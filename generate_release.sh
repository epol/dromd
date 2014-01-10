#!/bin/bash

OUTPUTFILE=progetto_achille_polesel.ml

cat dromd.ml | head -n 22 | sed -e 's/dromd.ml/'$OUTPUTFILE'/g' > $OUTPUTFILE
for SOURCE in syntax.ml semantic.ml dromd.ml 
do
    echo "Adding $SOURCE"
    cat $SOURCE | tail -n +22 | egrep -v '^#use' >> $OUTPUTFILE 
done

