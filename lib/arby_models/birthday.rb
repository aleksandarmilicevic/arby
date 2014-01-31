require 'arby/arby_dsl'

module ArbyModels
  extend Arby::Dsl
  alloy :Birthday do
	sig Name[]
	sig Date[]
	sig BirthdayBook[
		known: (set Name),
		date: known ** (one Date)
	]

	pred AddBirthday [
		bb, 
		bb1: BirthdayBook,
		n: Name, 
		d: Date] {
		#In Alloy bb'.date == bb.date ++ (n->d)
   			bb1.date == bb.date + (n ** d)  ## ++ does not any aRby syntex. using + for now.

    }

	pred DelBirthday [
		bb, 
		bb1: BirthdayBook, 
		n: Name] {
    		bb1.date == bb.date - (n ** Date)
    }

	pred FindBirthday [
		bb: BirthdayBook, 
		n: Name, d: 
		lone Date] {
    		d == bb.date(n) #
    }

	pred Remind [
		bb: BirthdayBook, today: Date, cards: set Name] {
    		cards = (bb.date).today
    }

	pred InitBirthdayBook [
		bb: BirthdayBook] {
    		no bb.known
    }

    assertion AddWorks {
    	all(bb, bb1: BirthdayBook, n: Name, d: Date, d1: (lone Date)) | # unclear on 
    	# how to implement the select. I saw this syntax {s: S | p1[s]} S.select{|s| p1(s)}
        if AddBirthday [bb,bb1,n,d] && FindBirthday [bb1,n,d1]
        	d == d1
        end
    }

	assertion DelIsUndo {
    	all (bb1,bb2,bb3: BirthdayBook, n: Name, d: Date) | #same select issue
        	if AddBirthday [bb1,bb2,n,d] && DelBirthday [bb2,bb3,n]
            	bb1.date == bb3.date
            end
    }
    
    #cmdDecl ::= ("run"|"check") fname "," scope
	#| ("run"|"check") "(" scope ")" block
    # check AddWorks for 3 but 2 BirthdayBook expect 0
    check AddWorks, 3 but 2 => BirthdayBook # not sure what to do with but and expect. 
    #Grandpa example had this run :ownGrandpa, Person => 4
    check DelIsUndo, 3 but 2 => BirthdayBook # not sure what to do with but and expect.

	pred BusyDay [
		bb: BirthdayBook, 
		d: Date]{
    		some (cards: set Name) | Remind [bb,d,cards] && !lone cards # unclear about this select
    	}


    run BusyDay, 3 but 1 => BirthdayBook# not sure what to do with but and expect.

  end
end