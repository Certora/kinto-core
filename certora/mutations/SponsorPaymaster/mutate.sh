mutateFileA="SponsorPaymaster"
mutateFileB=".sol"
imax=1
imin=1
i=$imin
while [ $i -ge $imin -a $i -le $imax ]
do
    cp ../../../src/paymasters/SponsorPaymaster.sol ./SponsorPaymaster_origin.sol
    file="$mutateFileA""$i""$mutateFileB"
    #echo $file
    cp $file ../../../src/paymasters/SponsorPaymaster.sol
    cd ../../../
    echo "$mutateFileA" "mutation" "$i"
    certoraRun ./certora/mutations/SponsorPaymaster/SponsorPaymaster.conf --msg "SponsorPaymaster mutation"" $i"
    echo "Mutation $i ran successfully"
    cd ./certora/mutations/SponsorPaymaster
    mv ./SponsorPaymaster_origin.sol ../../../src/paymasters/SponsorPaymaster.sol
    i=$(($i+1))
done