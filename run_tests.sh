file=$1

if [[ -z $file ]]
then
    file="test/test_suite.rb"
fi

bundle exec ruby -I"lib:test:.:../method_source/lib" $file $2 $3 $4 $5 $6 $7 $8 $9

