import React from 'react'
import {parseDiff} from '../../react-diff-view/src/parse'
import {getChangeKey} from '../../react-diff-view/src/utils'
import Diff from '../../react-diff-view/src/Diff'
import styled from "react-emotion"
import Prism from 'prismjs/components/prism-core'
import 'prismjs/plugins/keep-markup/prism-keep-markup'
require('prismjs/components/prism-lisp');

require('../../react-diff-view/src/Change.css');
require('../../react-diff-view/src/Diff.css');
require('../../react-diff-view/src/Hunk.css');
require('../../react-diff-view/src/Widget.css');

import diffnull0 from
  'raw-loader!../pages/introducing-the-pact-property-checker/steps/diffnull0';
import diff01 from
  'raw-loader!../pages/introducing-the-pact-property-checker/steps/diff01';
import diff12 from
  'raw-loader!../pages/introducing-the-pact-property-checker/steps/diff12';
import diff23 from
  'raw-loader!../pages/introducing-the-pact-property-checker/steps/diff23';
import diff34 from
  'raw-loader!../pages/introducing-the-pact-property-checker/steps/diff34';

let hunks0 = parseDiff(diffnull0)[0].hunks;
let hunks1 = parseDiff(diff01)[0].hunks;
let hunks2 = parseDiff(diff12)[0].hunks;
let hunks3 = parseDiff(diff23)[0].hunks;
let hunks4 = parseDiff(diff34)[0].hunks;

const Selectors = styled.div`
  display: flex;
  flex-direction: row;
`;

const Wrapper = styled.div`
  margin-top: 40px;
  font-size: 12pt;

  // the next two rules have the effect of removing the line number columns
  td.diff-gutter {
    visibility: collapse;
    width: 0;
  }

  tr.diff-hunk-header {
    display: none;
  }
`;

const WarningOuter = styled.div`
  background-color: #ffffc6;
  font-family: Consolas, Courier, monospace;
  margin-left: 0;
  padding: 10px;
  padding-left: 20px;
`;

const Button = styled.button`
  padding: 10px;
  margin: 10px;
  background: ${props => props.selected ? 'white' : 'transparent'};
  border: 2px solid white;
  cursor: pointer;
  outline: 0;
  box-shadow: none;
`;

const Description = styled.div`
  margin: 20px 0;
`;

const NoteOuter = styled.div`
  background-color: #ffffc6;
  font-family: Consolas, Courier, monospace;
  margin-left: 0;
  padding: 5px 0 5px 20px;
`;

function Note({ children }) {
  return (
    <NoteOuter>
      {children}
    </NoteOuter>
  );
}

function Warning({ children }) {
  return (
    <WarningOuter>
      <strong>Invalidating model found:</strong>
      <div
        // spacer
        style={{ height: '10px' }}
      />
      <div>{children}</div>
    </WarningOuter>
  );
}

const pages = [
  { hunks: hunks0,
    title: 'initial contract',
    preDescription: (
      <div>
        <p>
          In the initial version of our smart contract, the <code>transfer</code> function checks that the sender authorized the transfer (the transaction sent to the blockchain was signed by the sender) and that they have sufficient funds. It then updates both the sending (<code>from</code>) and receiving (<code>to</code>) account balances.
        </p>
        <p>
          Note that we start out with one property, using <code>row-enforced</code>. This states that the row indexed by <code>name</code> must have the keyset it contains (in its <code>ks</code> column) "enforced" in every possible code path. If the function's implementation enforces the keyset, the transaction will abort if it was not signed by the owner of that row.
        </p>
      </div>
      ),
      postDescription: '',
    widgets: {
      [getChangeKey(hunks0[0].changes[7])]: <Note>A schema describes the shape of a database row:</Note>,
      [getChangeKey(hunks0[0].changes[11])]: <Note>We create a table which contains rows of accounts:</Note>,
      [getChangeKey(hunks0[0].changes[16])]: <Note>Our first property on the function:</Note>,
    },
  },
  { hunks: hunks1,
    title: 'positive balance invariant',
    preDescription: (
      <div>
        <p>
          Let's add an invariant that account balances must be non-negative, to prevent overdrawn accounts.
        </p>
        <p>
          After we add the invariant, our tool reports back with example input to the function that it claims invalidates this invariant! And indeed, we forgot to check for a negative amount. It's good we checked this, because it turns out this bug would have allowed any user to drain (and even overdraw!) other users' accounts.
        </p>
      </div>
    ),
    postDescription: '',
    widgets: {
      [getChangeKey(hunks1[0].changes[13])]: (
<Warning><pre>{`Arguments:
    from := ""
    to := ""
    amount := -2

  Variables:
    from-bal := 1
    from-ks := KeySet 2
    to-bal := 1

  Reads:
    "" => { balance: 1, ks: KeySet 2 }
    "" => { balance: 1, ks: KeySet 2 }
    "" => { balance: 1, ks: KeySet 2 }

  Writes:
    "" => { balance: 3 }
    "" => { balance: -1 }

  Keysets:
    authorized:   database keyset at (accounts, 'ks, "")

  Result:
    "Write succeeded"
`}</pre></Warning>
      ),
    },
  },
  { hunks: hunks2,
    title: 'enforcing a positive transfer amount',
    preDescription: <p>The fix to this bug is simply to <code>enforce</code> that the amount we're transferring is positive:</p>,
    postDescription: '',
    widgets: {},
  },
  { hunks: hunks3,
    title: 'column conservation',
    preDescription: (
      <div>
        <p>
          Now we add a property to ensure that a transfer could never possibly destroy money, or create some out of thin air. This <code>column-conserves</code> property states that "the sum of all values in the <code>balance</code> column in the <code>accounts</code> table is preserved" across any possible transaction.
        </p>
        <p>
          The checker again reports back with an input to the function that it claims to invalidate this new mass conservation property. This time the balance (<code>1</code>) looks fine, but it's a bit suspicious that <code>from</code> and <code>to</code> are the same string.
        </p>
      </div>
    ),
    postDescription: (
      <div>
        <p>
          If we look closely at the last two lines of the function, we see that, given the provided inputs (<code>amount</code> set to <code>1</code> and a sender and receiver of the same account, <code>""</code>) we end up performing the following two writes:
        </p>
        <code>(update accounts "" {'{'} "balance": (- from-bal 1) })</code><br />
        <code>(update accounts "" {'{'} "balance": (+ to-bal 1) &nbsp;&nbsp;})</code>
        <p>
          Comparing to the <code>Writes</code>-section of the invalidating model report:
        </p>
        <pre>{`
        Writes:
          "" => { balance: 1 }
          "" => { balance: 3 }
        `}</pre>
        <p>
          This shows that, starting from a balance of 2, we first update the balance to be 1, and immediately then <em>overwrite that value</em> with 3. The net effect is that this set of inputs lets an attacker create money out of thin air!
        </p>
      </div>
    ),
    widgets: {
      [getChangeKey(hunks3[0].changes[16])]: (
<Warning><pre>{`Arguments:
    from := ""
    to := ""
    amount := 1

  Variables:
    from-bal := 2
    from-ks := KeySet 4
    to-bal := 2

  Reads:
    "" => { balance: 2, ks: KeySet 4 }
    "" => { balance: 2, ks: KeySet 4 }
    "" => { balance: 2, ks: KeySet 4 }

  Writes:
    "" => { balance: 1 }
    "" => { balance: 3 }

  Keysets:
    authorized:   database keyset at (accounts, 'ks, "")

  Result:
    "Write succeeded"
`}</pre></Warning>
      )
    },
  },
  { hunks: hunks4,
    title: 'another fix',
    preDescription: <p>To address this bug, we can simply <code>enforce</code> that the sender and recipient are not the same account. At this point, the property checker reports that all properties and invariants validate for all possible inputs!</p>,
    postDescription: '',
    widgets: {},
  }
];

export default function AnnotatedCode() {
  let renderedPages = pages.map(({hunks, preDescription, postDescription, widgets, title}, index) => (
    <Wrapper key={index}>
      <h2>Step {index + 1}: {title}</h2>
      <Description>{preDescription}</Description>
      <Diff
        hideGutter={true}
        // hack to get prism to detect the language
        className="language-lisp"
        hunks={hunks}
        viewType="unified"
        widgets={widgets}
        onRenderCode={elem => Prism.highlightElement(elem)}
      />
      <Description>{postDescription}</Description>
    </Wrapper>
  ));

  return (
    <div>
      {renderedPages}
    </div>
  );
}
