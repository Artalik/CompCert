tree.vo tree.glob tree.v.beautified tree.required_vo: tree.v 
tree.vio: tree.v 
tree.vos tree.vok tree.required_vos: tree.v 
example1.vo example1.glob example1.v.beautified example1.required_vo: example1.v tree.vo
example1.vio: example1.v tree.vio
example1.vos example1.vok example1.required_vos: example1.v tree.vos
freefresh.vo freefresh.glob freefresh.v.beautified freefresh.required_vo: freefresh.v tree.vo
freefresh.vio: freefresh.v tree.vio
freefresh.vos freefresh.vok freefresh.required_vos: freefresh.v tree.vos
fresh.vo fresh.glob fresh.v.beautified fresh.required_vo: fresh.v freefresh.vo tree.vo
fresh.vio: fresh.v freefresh.vio tree.vio
fresh.vos fresh.vok fresh.required_vos: fresh.v freefresh.vos tree.vos
example2.vo example2.glob example2.v.beautified example2.required_vo: example2.v tree.vo freefresh.vo fresh.vo
example2.vio: example2.v tree.vio freefresh.vio fresh.vio
example2.vos example2.vok example2.required_vos: example2.v tree.vos freefresh.vos fresh.vos
SepSet.vo SepSet.glob SepSet.v.beautified SepSet.required_vo: SepSet.v 
SepSet.vio: SepSet.v 
SepSet.vos SepSet.vok SepSet.required_vos: SepSet.v 
example3.vo example3.glob example3.v.beautified example3.required_vo: example3.v tree.vo freefresh.vo fresh.vo SepSet.vo
example3.vio: example3.v tree.vio freefresh.vio fresh.vio SepSet.vio
example3.vos example3.vok example3.required_vos: example3.v tree.vos freefresh.vos fresh.vos SepSet.vos
