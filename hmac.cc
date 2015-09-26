#include "hmac.h"
#include <ktcommon.h>
#include <iostream>
#include <openssl/hmac.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <unistd.h>
#include <time.h>
#include <cassert>

//==========================================================================
void  Random::init () {
    int  fd;

    fd = open ("/dev/urandom", O_RDONLY);
    if (fd < 0)
	assert (0);
    read (fd, &seed, sizeof (seed));
    close (fd);
    srandom (seed);
}

std::string  Random::randomKey () {
    char  b[32];

    enc (random (), b);
    enc (random (), b + 5);
    enc (random (), b + 10);
    enc (random (), b + 15);
    return std::string (b, 20);
}

void  Random::enc (unsigned long v, char* b) {
    static const std::string  SaltChar (CharConst ("ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789"));
    static int  n = SaltChar.size ();
    int  i;

    for (i = 0; i < 5; i ++) {
	b[i] = SaltChar[v % n];
	v /= n;
    }
}

//==========================================================================
bool  HMacSignature::loaddb () {
    if (pathKeymap) {
	if (checkKeymapStat ()) {
	    loaddb_in ();
	    return true;
	}
    }
    return false;
}

bool  HMacSignature::checkKeymapStat () {
    struct stat  st;
    if (stat (pathKeymap, &st)) {
	return false;
    } else {
	if (keymap) {
	    if (st.st_dev == prevStat.st_dev && st.st_ino == prevStat.st_ino && st.st_mtime == prevStat.st_mtime) {
		return false;
	    } else {
		memcpy (&prevStat, &st, sizeof (st));
		return true;
	    }
	} else {
	    memcpy (&prevStat, &st, sizeof (st));
	    return true;
	}
    }
}

void  HMacSignature::loaddb_in () {
    int  fd;
    fd = open (pathKeymap, O_RDONLY);
    if (fd >= 0) {
	std::string  text;
	text.resize (prevStat.st_size);
	read (fd, (void*)text.data (), prevStat.st_size);
	close (fd);

	delete keymap_b;
	keymap_b = NULL;
	std::map<std::string, std::string>*  map = new std::map<std::string, std::string>;
	std::string::const_iterator  b, e;
	b = text.begin ();
	e = text.end ();
	while (b < e) {
	    std::string::const_iterator  s, p;
	    for (s = b; s < e && *s != '\n'; ++ s) {}
	    for (p = b; p < s && *p != '\t'; ++ p) {}
	    if (b < p) {
		std::string  key (b, p);
		for (; p < s && *p == '\t'; ++ p) {}
		if (p < s) {
		    std::string  sec (p, s);
		    (*map)[key] = sec;
		}
	    }
	    for (; s < e && *s == '\n'; ++ s) {}
	    b = s;
	}
	keymap_b = keymap;
	keymap = map;
	map = NULL;
    }
}

//==========================================================================
std::string  base64encode (const std::string& data) {
    const char*  tbl = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";
    std::string::const_iterator  rp = data.begin ();
    size_t  size = data.size ();
    std::string  ans;

    for (size_t i = 0; i < size; i += 3) {
	switch (size - i) {
	case 1:
	    ans.append (1, tbl[(unsigned char)*rp >> 2]);
	    ans.append (1, tbl[((unsigned char)*rp++ & 3) << 4]);
	    ans.append (1, '=');
	    ans.append (1, '=');
	    break;
	case 2:
	    ans.append (1, tbl[(unsigned char)*rp >> 2]);
	    ans.append (1, tbl[(((unsigned char)*rp++ & 3) << 4) + ((unsigned char)*rp >> 4)]);
	    ans.append (1, tbl[((unsigned char)*rp++ & 0xf) << 2]);
	    ans.append (1, '=');
	    break;
	default:
	    ans.append (1, tbl[(unsigned char)*rp >> 2]);
	    ans.append (1, tbl[(((unsigned char)*rp++ & 3) << 4) + ((unsigned char)*rp >> 4)]);
	    ans.append (1, tbl[(((unsigned char)*rp++ & 0xf) << 2) + ((unsigned char)*rp >> 6)]);
	    ans.append (1, tbl[(unsigned char)*rp++ & 0x3f]);
	    break;
	}
    }
    return ans;
}

std::string  base64decode (const std::string& data) {
    std::string::const_iterator  b = data.begin ();
    std::string::const_iterator  e = data.end ();
    size_t  eqcnt = 0;
    std::string  ans;

    while (b < e && eqcnt == 0) {
	size_t  bits = 0;
	size_t  i;
	for (i = 0; b < e && i < 4; ++ b) {
	    if (*b >= 'A' && *b <= 'Z') {
		bits = (bits << 6) | (*b - 'A');
		++ i;
	    } else if (*b >= 'a' && *b <= 'z') {
		bits = (bits << 6) | (*b - 'a' + 26);
		++ i;
	    } else if (*b >= '0' && *b <= '9') {
		bits = (bits << 6) | (*b - '0' + 52);
		++ i;
	    } else if (*b == '+') {
		bits = (bits << 6) | 62;
		++ i;
	    } else if (*b == '/') {
		bits = (bits << 6) | 63;
		++ i;
	    } else if (*b == '=') {
		bits <<= 6;
		++ i;
		++ eqcnt;
	    }
	}
	if (i == 0 && b >= e) continue;
	switch (eqcnt) {
	case 0:
	    ans.append (1, (bits >> 16) & 0xff);
	    ans.append (1, (bits >> 8) & 0xff);
	    ans.append (1, bits & 0xff);
	    break;
	case 1:
	    ans.append (1, (bits >> 16) & 0xff);
	    ans.append (1, (bits >> 8) & 0xff);
	    break;
	case 2:
	    ans.append (1, (bits >> 16) & 0xff);
	    break;
	}
    }
    return ans;
}

std::string  hmac_sha256 (const std::string& key, const std::string& data) {
    unsigned char  md[EVP_MAX_MD_SIZE];
    unsigned int  md_len;

    HMAC (EVP_sha256 (), key.c_str (), key.length (), uchar_type (data.c_str ()), data.length (), md, &md_len);

    return std::string (char_type (md), md_len);
}

static bool  matchSkip (std::string::const_iterator& b, std::string::const_iterator e, const char* t, size_t s) {
    if (b + s <= e && memcmp (t, &b[0], s) == 0) {
	b += s;
	return true;
    } else {
	return false;
    }
}

static int  skipInt (std::string::const_iterator& b, std::string::const_iterator e) {
    int  ans = 0;
    while (b < e && '0' <= *b && *b <= '9') {
	ans = ans * 10 + (*b - '0');
	++ b;
    }
    return ans;
}

bool  readHttpDate (const std::string& date, uint64_t& t) {
    std::string  idate = date;
    kyototycoon::kc::strtolower (&idate);
    std::string::const_iterator  b, e;
    b = idate.begin ();
    e = idate.end ();
    struct tm  tm;
    memset (&tm, 0, sizeof (tm));
    for (; b < e && *b == ' '; ++ b) {}
    if (matchSkip (b, e, CharConst ("sun,"))) {
    } else if (matchSkip (b, e, CharConst ("mon,"))) {
    } else if (matchSkip (b, e, CharConst ("tue,"))) {
    } else if (matchSkip (b, e, CharConst ("wed,"))) {
    } else if (matchSkip (b, e, CharConst ("thu,"))) {
    } else if (matchSkip (b, e, CharConst ("fri,"))) {
    } else if (matchSkip (b, e, CharConst ("sat,"))) {
    } else {
	return false;
    }
    for (; b < e && *b == ' '; ++ b) {}
    tm.tm_mday = skipInt (b, e);
    for (; b < e && *b == ' '; ++ b) {}
    if (matchSkip (b, e, CharConst ("jan"))) {
	tm.tm_mon = 0;
    } else if (matchSkip (b, e, CharConst ("feb"))) {
	tm.tm_mon = 1;
    } else if (matchSkip (b, e, CharConst ("mar"))) {
	tm.tm_mon = 2;
    } else if (matchSkip (b, e, CharConst ("apr"))) {
	tm.tm_mon = 3;
    } else if (matchSkip (b, e, CharConst ("may"))) {
	tm.tm_mon = 4;
    } else if (matchSkip (b, e, CharConst ("jun"))) {
	tm.tm_mon = 5;
    } else if (matchSkip (b, e, CharConst ("jul"))) {
	tm.tm_mon = 6;
    } else if (matchSkip (b, e, CharConst ("aug"))) {
	tm.tm_mon = 7;
    } else if (matchSkip (b, e, CharConst ("sep"))) {
	tm.tm_mon = 8;
    } else if (matchSkip (b, e, CharConst ("oct"))) {
	tm.tm_mon = 9;
    } else if (matchSkip (b, e, CharConst ("nov"))) {
	tm.tm_mon = 10;
    } else if (matchSkip (b, e, CharConst ("dec"))) {
	tm.tm_mon = 11;
    } else {
	return false;
    }
    for (; b < e && *b == ' '; ++ b) {}
    tm.tm_year = skipInt (b, e) - 1900;
    for (; b < e && *b == ' '; ++ b) {}
    tm.tm_hour = skipInt (b, e);
    if (*b == ':') ++ b; else return false;
    tm.tm_min = skipInt (b, e);
    if (*b == ':') ++ b; else return false;
    tm.tm_sec = skipInt (b, e);
    for (; b < e && *b == ' '; ++ b) {}
    if (matchSkip (b, e, CharConst ("gmt"))) {
	tm.tm_isdst = 0;
	tm.tm_gmtoff = 0;
    } else {
	return false;
    }
    t = timegm (&tm);
    return true;
}
