mutateFileA="KintoID"
mutateFileB=".sol"
imax=7
imin=7
i=$imin
file_origin=../../munged/KintoID_origin.sol
while [ $i -ge $imin -a $i -le $imax ]
do
    cp ../../../src/KintoID.sol ./KintoID_origin.sol
    file="$mutateFileA""$i""$mutateFileB"
    diff -uN "$file_origin" "$file" | sed 's+\'"$file_origin"'/++g' | sed 's+'"$file"'++g' > "diff.patch"
    #echo $file
    patch ../../../src/KintoID.sol < "diff.patch"
    cd ../../../    
    echo "$mutateFileA" "mutation" "$i"
    certoraRun ./certora/mutations/KintoID/KintoID_SanctionsTraits.conf --msg "KintoID Sanctions-ERC721 mutation"" $i"
    echo "Mutation $i ran successfully"
    cd ./certora/mutations/KintoID
    mv ./KintoID_origin.sol ../../../src/KintoID.sol
    i=$(($i+1))
done