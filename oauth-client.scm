;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; OAuth 1.0, 1.0a & RFC 5849
;;;
;;;  Copyright (C) 2012 -> 2014, Andy Bennett
;;;  All rights reserved.
;;;
;;;  Redistribution and use in source and binary forms, with or without
;;;  modification, are permitted provided that the following conditions are met:
;;;
;;;  Redistributions of source code must retain the above copyright notice, this
;;;  list of conditions and the following disclaimer.
;;;  Redistributions in binary form must reproduce the above copyright notice,
;;;  this list of conditions and the following disclaimer in the documentation
;;;  and/or other materials provided with the distribution.
;;;  Neither the name of the author nor the names of its contributors may be
;;;  used to endorse or promote products derived from this software without
;;;  specific prior written permission.
;;;
;;;  THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
;;;  AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
;;;  IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
;;;  ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDERS OR CONTRIBUTORS BE
;;;  LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
;;;  CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
;;;  SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
;;;  INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
;;;  CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
;;;  ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
;;;  POSSIBILITY OF SUCH DAMAGE.
;;;
;;; Andy Bennett <andyjpb@knodium.com>, 2012/10
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(module oauth-client
	(empty-credential
	  make-oauth-credential
	  token
	  secret
	  make-oauth-service-provider
	  make-oauth-service
	  oauth-service
	  oauth-protocol-parameters
	  oauth-token-credential
	  with-oauth
	  authenticated-call-with-input-request
	  call-with-input-request
	  acquire-temporary-credential
	  authorize-resource-owner
	  acquire-token-credential)

(import chicken scheme)


; Units - http://api.call-cc.org/doc/chicken/language
(use data-structures extras srfi-1 srfi-13)

; Eggs - http://wiki.call-cc.org/chicken-projects/egg-index-4.html
(use uri-common intarweb hmac sha1 base64)
(require-library http-client)
(import (rename http-client (call-with-input-request orig:call-with-input-request)))



(define supported-signatures   '(plaintext hmac-sha1)) ; '(plaintext hmac-sha1 rsa-sha1)
(define supported-methods      '(POST)) ; '(POST GET)
(define supported-transmission '(authorization-header)) ; '(authorization-header request-entity-body query-string)

; Differences between 1.0 and 1.0a
;   http://code.google.com/p/oauth/source/diff?spec=svn1058&old=991&r=1058&format=unidiff&path=%2Fspec%2Fcore%2F1.0a%2Foauth-core-1_0a.xml
;     + oauth_callback in temporary credential acquisition rather than owner auth
;     + oauth_callback_confirmed in temporary credential response
;     + presence of oauth_verifier in owner auth callback query string
;     + in absence of callback, display of verification code rather than assertion that auth has completed.
; Differences between 1.0a and rfc5849
;   http://tools.ietf.org/html/rfc5849#appendix-A
;     + MUST use TLS/SSL with PLAINTEXT
;     + nonce and timestamp parameters OPTIONAL when using PLAINTEXT
;     + permitted omitting empty oauth_token
;     + various other things only relevant for non PLAINTEXT signatures
(define supported-versions ; List of (version oauth_version-string)
  '((1.0     . "1.0")
    (1.0a    . "1.0a")
    (rfc5849 . "rfc5849")))


(define (memv? obj lst) (and (memv obj lst) #t))
(define %encode uri-encode-string)

; Some OAuth servers return form-urlencoded responses with trailing \r.
(define (read-reply port)
 (string-chomp (read-string #f port) "\r"))

(define (signature-base-string request protocol-parameters body)
  (let* ((uri   (request-uri request))
	 (port  (uri-port uri))
	 (query (uri-query uri))
	 (path  (uri-path uri))
	 (base-string-uri
	   (conc
	     (uri->string
	       (update-uri uri ; Apply RFC5849: Section 3.4.1.2 Constraints
			   host: (string-downcase (uri-host uri))
			   port: (case (uri-scheme uri)
				   ((http)  (if (or (equal? port 80)  (not port)) #f port))
				   ((https) (if (or (equal? port 443) (not port)) #f port)))
			   query: #f
			   fragment: #f))
	     (if (null? path) "/" "")))
	 (normalised-request-parameters ; Request Parameters as per RFC5849: Section 3.4.1.3
	   (string-intersperse
	     (map
	       (lambda (param)
		 (conc (car param) "=" (cdr param)))
	       (sort
		 (fold ; Encoding for Parameter Normalisation as per RFC5849: Section 3.4.1.3.2
		   (lambda (param seed) ; %encode's (uri-encode-string) default char-set matches RFC5849: Section 3.6
		     (if (cdr param) ; Omit keys with #f values as per uri-common's form-urlencode.
		       (cons
			 (cons
			   (%encode (->string (car param)))
			   (if (eqv? #t (cdr param)) ; Handle keys with #t value as per uri-common's form-urlencode.
			     ""
			     (%encode (->string (cdr param)))))
			 seed)
		       seed))
		   '()
		   (alist-delete
		     'oauth-signature
		     (append
		       query
		       (alist-delete 'realm protocol-parameters) ; Future contents of the "Authorization" header
		       (if (list? body) ; HTTP request entity-body if relevant
			 body
			 '()))))
		 (lambda (a b)
		   (if (string=? (car a) (car b))
		     (string<? (cdr a) (cdr b))
		     (string<? (car a) (car b))))))
	     "&")))
    (conc
      (%encode (string-upcase (symbol->string (request-method request))))
      "&"
      (%encode base-string-uri)
      "&"
      (%encode normalised-request-parameters))))

(define (sign-request request protocol-parameters body service token-credential)
  ; For hmac-sha1 and rsa-sha1 we must assert the http request entity-body conditions of RFC5849: Section 3.4.1.3.1
  (let ((signature-method (alist-ref 'signature-method service)))
    (case signature-method
      ((plaintext) ; RFC5849: Section 3.4.4 - MUST be used with TLS/SSL.
       ;(assert (eqv? 'https (uri-scheme (request-uri request))))
       (let ((client-credential (alist-ref 'client-credential service)))
	 (conc (%encode (secret client-credential)) "&" (%encode (secret token-credential)))))
      ((hmac-sha1)
       (let* ((signature-base-string (signature-base-string request protocol-parameters body))
	      (client-credential     (alist-ref 'client-credential service))
	      (key                   (conc (%encode (secret client-credential)) "&" (%encode (secret token-credential)))))
	 (base64-encode ((hmac key (sha1-primitive)) signature-base-string))))
      (else (abort (conc signature-method " signature method not implemented!"))))))


; The default Authorization unparser supplied by inaterweb generates an
; "Authorization: Oauth ..." header. The OAuth spec calls for
; "Authorization: OAuth ..." but HTTP declares it as case-insensitive:
;
; "HTTP provides a simple challenge-response authentication mechanism that MAY
; be used by a server to challenge a client request and by a client to provide
; authentication information. It uses an extensible, case-insensitive token to
; identify the authentication scheme, followed by a comma-separated list of
; attribute-value pairs which carry the parameters necessary for achieving
; authentication via that scheme."
;  -- RFC2617, section 1.2
;
; Some service providers have bugs that require OAuth to be capitalized exactly
; as defined in the OAuth spec. Therefore, we copy the authorization-unparser
; from intarweb and modify it to output OAuth with the expected capitalisation.
;
(define (authorization-unparser header-contents)
  (let loop ((headers (reverse header-contents))
             (result '()))
    (if (null? headers)
        result
        (let* ((default-unparser        ; Not great, but better than nothing
                 (lambda (params) (unparse-params params '())))
               (auth-scheme (get-value (car headers)))
               (unparser (alist-ref auth-scheme
                                    (authorization-param-subunparsers)
                                    eq? default-unparser))
               (unparsed-value (sprintf "~A ~A"
					(if (eq? auth-scheme 'oauth) "OAuth" (symbol->http-name auth-scheme))
                                        (unparser (get-params (car headers))))))
          (loop (cdr headers) (cons unparsed-value result))))))

(header-unparsers (alist-update! 'authorization authorization-unparser (header-unparsers)))


(authorization-param-subunparsers
  (alist-cons
    'oauth
    (lambda (params)
      (string-intersperse
	(map (lambda (p)
	       (conc  (%encode (symbol->string (car p))) "=\"" (%encode (->string (cdr p))) "\""))
	     params)
      ", "))
    (authorization-param-subunparsers)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Tools for managing Credentials
;;;
(define empty-credential  '("" . ""))

(define (make-oauth-credential identifier secret)
  (cons identifier secret))

(define token  car)
(define secret cdr)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Tools for defining Service Providers
;;;   Particulars specified by RFC5849, Section 2
;;;
(define (make-oauth-service-provider #!key protocol-version signature-method owner-auth-url
				     credential-request-url (credential-request-method 'POST)
				     token-request-url (token-request-method 'POST)
				     (transmission-method 'authorization-header))
  (assert (memv protocol-version (map car supported-versions)))
  (assert (string? credential-request-url))
  (assert (string? owner-auth-url))
  (assert (string? token-request-url))
  (assert (memv signature-method supported-signatures))
  (assert (memv credential-request-method supported-methods))
  (assert (memv token-request-method supported-methods))
  (assert (memv transmission-method supported-transmission))

  (let ((credential-request-url (uri-reference credential-request-url))
	(owner-auth-url         (uri-reference owner-auth-url))
	(token-request-url      (uri-reference token-request-url)))
    (assert (eqv? 'https (uri-scheme credential-request-url)))
    (assert (eqv? 'https (uri-scheme token-request-url)))

    `((protocol-version       . ,protocol-version)
      (signature-method       . ,signature-method)
      (credential-request-req . ,(make-request uri:    credential-request-url
					       method: credential-request-method))
      (owner-auth-url         . ,owner-auth-url)
      (token-request-req      . ,(make-request uri:    token-request-url
					       method: token-request-method))
      (confirms-callback      . ,(memv? protocol-version '(1.0a rfc5849)))
      (callback-on-credential . ,(memv? protocol-version '(1.0a rfc5849)))
      (callback-on-owner-auth . ,(memv? protocol-version '(1.0)))
      (sends-oauth-verifier   . ,(memv? protocol-version '(1.0a rfc5849))))))


(define (make-oauth-service #!key service client-credential)
 (alist-cons 'client-credential client-credential service))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;(define call-with-input-request orig:call-with-input-request)
;(define (with-oauth service token-credential thunk)
;  (fluid-let ((call-with-input-request
;		(cut authenticated-call-with-input-request service '() token-credential <> <> <>)))
;	      (thunk)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Authenticated Requests - RFC 5849, Section 3
;;;   For making calls to OAuth protected APIs
;;;
(define oauth-service             (make-parameter #f))
(define oauth-protocol-parameters (make-parameter '()))
(define oauth-token-credential    (make-parameter empty-credential))

(define (with-oauth service token-credential thunk)
  (parameterize ((oauth-service service)
		 (oauth-token-credential token-credential))
		(thunk)))

(define (authenticated-call-with-input-request service protocol-parameters token-credential uri-or-request writer reader)
  (let* ((uri (cond ((uri? uri-or-request) uri-or-request) ; stolen from http-client
		    ((string? uri-or-request) (uri-reference uri-or-request))
		    (else (request-uri uri-or-request))))
	 (req (if (request? uri-or-request) ; stolen from http-client
		uri-or-request
		(make-request uri: uri method: (if writer 'POST 'GET))))
	 (body (if (list? writer) writer #f)) ; RFC5849: Section 3.4.1.3.1. Parameter Sources
	 (signature-method (alist-ref 'signature-method service))
	 (protocol-parameters
	   (append protocol-parameters
		   `((oauth_consumer_key     . ,(token (alist-ref 'client-credential service)))
		     (oauth_token            . ,(token token-credential))
		     (oauth_signature_method . ,(string-upcase (symbol->string signature-method)))
		     (oauth_version          . ,(alist-ref (alist-ref 'protocol-version service) supported-versions equal?))
		     ,@(if (not (eqv? 'plaintext signature-method))
			 `((oauth_timestamp . ,(inexact->exact (current-seconds)))
			   (oauth_nonce . 1))
			 '()))))
	 (signature (sign-request req protocol-parameters body service token-credential))
	 (protocol-parameters (alist-cons 'oauth_signature signature protocol-parameters)))
    (orig:call-with-input-request
      (update-request
	req
	headers: (headers `((authorization . (#(oauth ,protocol-parameters))))))
      (or body writer)
      reader)))

(define (call-with-input-request uri-or-request writer reader)
  (assert (oauth-service))
  (authenticated-call-with-input-request (oauth-service) (oauth-protocol-parameters) (oauth-token-credential) uri-or-request writer reader))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Redirection-Based Authorization - RFC 5849, Section 2
;;;   For provisioning the tokens
;;;
(define (acquire-temporary-credential service #!optional callback-url)
  (let* ((callback-on-credential (alist-ref 'callback-on-credential service))
	 (_ (if (and (not callback-on-credential) callback-url)
	     (abort "This service does not accept callback-url during temporary credential acquisition.")))
	 (resp
	   (nth-value 0 (authenticated-call-with-input-request
			  service
			  `(,@(if (and callback-on-credential callback-url)
				`((oauth_callback . ,callback-url))
				'()))
			  empty-credential
			  (alist-ref 'credential-request-req service)
			  "" ; forces POST even if credential-request-req isn't a request object.
			  (lambda (p) (form-urldecode (read-reply p))))))
	 (credential (make-oauth-credential
		       (alist-ref 'oauth_token resp eqv? "")
		       (alist-ref 'oauth_token_secret resp eqv? "")))
	 (_ (if (alist-ref 'confirms-callback service)
	      (assert (alist-ref 'oauth_callback_confirmed resp)))) ; RFC5849: Section 2.1
	 (rest (remove
		 (lambda (e) (memv (car e) '(oauth_token_secret oauth_token oauth_callback_confirmed)))
		 resp)))
    (values credential rest)))

(define (authorize-resource-owner service temporary-credential #!optional callback-url)
  (let* ((callback-on-owner-auth (alist-ref 'callback-on-owner-auth service))
	 (_ (if (and (not callback-on-owner-auth) callback-url)
	      (abort "This service does not accept callback-url during resource owner authorization.")))
	 (callback-url (cond ((uri? callback-url) (uri->string callback-url))
			     (else callback-url)))
	 (uri (alist-ref 'owner-auth-url service))
	 (query (uri-query uri))
	 (query (alist-cons 'oauth_token (token temporary-credential) query))
	 (query (if (and callback-on-owner-auth callback-url)
		  (alist-cons 'oauth_callback callback-url query)
		  query))
	 (uri (update-uri uri query: query)))
  uri)) ; return a uri object that the user can be redirected to.

(define (acquire-token-credential service temporary-credential #!optional verifier)
  (if (and
	(alist-ref 'sends-oauth-verifier service)
	(not verifier))
    (abort "oauth_verifier MUST be supplied for this service!"))
  (let* ((resp (nth-value 0 (authenticated-call-with-input-request
			      service
			      (if verifier `((oauth_verifier . ,verifier)) '())
			      temporary-credential
			      (alist-ref 'token-request-req service)
			      ""; forces POST even if token-request-req isn't a request object.
			      (lambda (p) (form-urldecode (read-reply p))))))
	 (credential (make-oauth-credential
		       (alist-ref 'oauth_token resp eqv? "")
		       (alist-ref 'oauth_token_secret resp eqv? "")))
	 (rest (remove
		 (lambda (e) (memv (car e) '(oauth_token_secret oauth_token)))
		 resp)))
    (values credential rest)))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

)

