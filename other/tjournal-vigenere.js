# test from https://tjournal.ru/etc/passwd
# answers:
const alphabet = [...'абвгдеёжзийклмнопрстуфхцчшщъыьэюя'];
console.log('alphabet:', alphabet.join());

function to_number(ch) {
    return alphabet.indexOf(ch);
}

console.log('as numbers:', alphabet.map(to_number).join());

function from_number(n) {
    return alphabet[n];
}

console.log('from numbers:', alphabet.map(to_number).map(from_number).join());

const key = [...'морфиус'].map(to_number);
const chipher = 'фтхёе аапър хдён чярёсхсл ещжиёс хц дбцвы чьщчс, ба яй агфжихжм жчянчэ нжс ьгвэфвдш хмьюпн: вххь,фци,гряк,югфп,дэч,зщыовс 21,26,30,23,14,56. юябнбрц чё бнедмыщ э кедмрм ц увх.';

// http://www.wikiwand.com/en/Vigen%C3%A8re_cipher
function decrypt(str, key) {
    const arr = [...str];
    const res = [];
    let j = 0;
    for(let i = 0; i < arr.length; i++) {
        const ch = arr[i];
        if(alphabet.includes(ch)) {
            const d = (to_number(ch) - key[j] + alphabet.length) % alphabet.length;
            j = (j + 1) % key.length;
            res.push(from_number(d));
        } else {
            res.push(ch);
        }
    }
    return res.join('');
}

console.log(decrypt(chipher, key));
// здесь могла быть красивая цитата из умной книги, но ты получишь только эти исходные данные:
// один,два,пять,ноль,три,четыре 21,26,30,23,14,56.
// поменяй их местами и вставь в код.

function getSequence(str1, str2) {
    const arr1 = str1.split(',');
    const arr2 = str2.split(',');

    let i = 0;
    let arr3 = arr2.map(n => i = arr2[i]);
    console.log('i:', i, ', arr3:', arr3.join());
    let result = '%s-%s-%s-%s-%s-%s';
    arr3.forEach(n => {
        result = result.replace('%s', arr1[n]);
    });
    return result;
}

console.log('answer:', getSequence('21,26,30,23,14,56', '1,2,5,0,3,4'));

console.log(decrypt('Я — хцсеибязш', [...'морфиус'].map(to_number)));
// Я — избранный
