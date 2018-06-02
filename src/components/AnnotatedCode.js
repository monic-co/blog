import React from 'react'
import {parseDiff, getChangeKey, Diff} from 'react-diff-view'
import styled from "react-emotion"
import Prism from 'prismjs/components/prism-core'
import 'prismjs/plugins/keep-markup/prism-keep-markup'
import loadLanguages from 'prismjs/components/index.js'
loadLanguages(['lisp']);

require('react-diff-view/src/Change.css');
require('react-diff-view/src/Diff.css');
require('react-diff-view/src/Hunk.css');
require('react-diff-view/src/Widget.css');

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
  }
  table.diff {
    margin-left: -14ch;
  }

  tr.diff-hunk-header {
    display: none;
  }
`;

const Warning = styled.div`
  background-color: #ffffc6;
  font-family: Consolas, Courier, monospace;
  margin-left: 123px;
  border-left: 1px solid white;
  padding: 10px 0 5px 20px;
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

const Note = styled.div`
  font-family: Consolas, Courier, monospace;
  margin-left: 123px;
  border-left: 1px solid white;
  padding: 10px 0 5px 20px;
`;

const pages = [
  { hunks: hunks0,
    title: 'Initial contract',
    description: (
      <div>
        <p>
          In the initial version of our smart contract, the <code>transfer</code> function checks that the sender authorized the transfer (by signing the transaction sent to the blockchain) and that they have sufficient funds. It then updates both the sending (<code>from</code>) and receiving (<code>to</code>) account balances.
        </p>
        <p>
          Note that we start out with one property, using <code>row-enforced</code>. This states that the row indexed by <code>name</code> must have the keyset it contains (in its <code>ks</code> column) "enforced" in every possible code path. If the function's implementation enforces the keyset, the transaction will abort if it was not signed by "owner" of that row.
        </p>
      </div>
      ),
    widgets: {
      [getChangeKey(hunks0[0].changes[5])]: <Note>A schema describes the shape of a database row:</Note>,
      [getChangeKey(hunks0[0].changes[9])]: <Note>We create a table which contains rows of accounts:</Note>,
      [getChangeKey(hunks0[0].changes[14])]: <Note>Our first property on the function:</Note>,
    },
  },
  { hunks: hunks1,
    title: 'Positive balance invariant',
    description: (
      <div>
        <p>
          Let's add an invariant that account balances must be non-negative, because this seems like something that should always be true.
        </p>
        <p>
          In response, our tool reports back with example input to the function that it claims invalidates this invariant! And indeed, we forgot to check for a negative amount. It's good we checked this, because it turns out this bug would have allowed any user to drain (and even overdraw!) other users' accounts.
        </p>
      </div>
    ),
    widgets: {
      [getChangeKey(hunks1[0].changes[13])]: <Warning>(invariant) Invalidating model found: from = "" :: String, to = "" :: String, amount = -39 :: Integer</Warning>,
    },
  },
  { hunks: hunks2,
    title: 'Enforcing a positive transfer amount',
    description: <p>The fix to this bug is simply to <code>enforce</code> that the amount we're transferring is positive:</p>,
    widgets: {},
  },
  { hunks: hunks3,
    title: 'Column conservation',
    description: (
      <div>
        <p>
          Now we add a property to ensure that a transfer could never possibly destroy money, or create some out of thin air. This <code>column-conserves</code> property states that "the sum of all values in the <code>balance</code> column in the <code>accounts</code> table is preserved" across any possible transaction.
        </p>
        <p>
          The checker again reports back with an input to the function that it claims to invalidate this new mass conservation property. This time the balance (<code>1</code>) looks fine, but it's a bit suspicious that <code>from</code> and <code>to</code> are the same string.
        </p>
        <p>
          <b>[ TODO TODO TODO, move this *below* the code ]</b>
          If we look closely at the last two lines of the function, we see that, given the provided inputs (<code>amount</code> set to <code>1</code> and a sender and receiver of the same account, <code>""</code>) we end up performing the following two writes:
        </p>
        <code>(update accounts "" {'{'} "balance": (- from-bal 1) }) ; This write is moot.</code><br />
        <code>(update accounts "" {'{'} "balance": (+ to-bal 1) &nbsp;&nbsp;})</code>
        <p>
          writing the new balance as <code>from-bal - 1</code> and immediately then <em>overwriting</em> it with <code>to-bal + 1</code>. The net effect is that this set of inputs lets an attacker create $1 out of thin air!
        </p>
      </div>
    ),
    widgets: {
      [getChangeKey(hunks3[0].changes[16])]: <Warning>Invalidating model found: from = "" :: String, to = "" :: String, amount = 1 :: Integer</Warning>,
    },
  },
  { hunks: hunks4,
    title: 'Another fix',
    description: <p>To address this bug, we can simply <code>enforce</code> that the sender and recipient are not the same account. At this point, the property checker reports that all properties and invariants are validate for all possible inputs!</p>,
    widgets: {},
  }
];

export default class AnnotatedCode extends React.Component {
  constructor(props) {
    super(props);
    this.state = { tabIndex: 0 };
  }

  componentDidMount() {
    document.onkeydown = e => {
      switch (e.keyCode) {
        case 37: // left arrow
          this.setState(({tabIndex}) =>
            ({tabIndex: Math.max(tabIndex - 1, 0)})
          );
          break;
        case 39: // right arrow
          this.setState(({tabIndex}) =>
            ({tabIndex: Math.min(tabIndex + 1, pages.length - 1)})
          );
          break;
      }
    };
  }

  render() {
    let {tabIndex} = this.state;
    let {hunks, description, widgets} = pages[tabIndex];

    let tabs = (
      <Selectors>
        {pages.map(({title}, index) =>
          <Button
            key={index}
            selected={index == tabIndex}
            onClick={() => this.setState({tabIndex: index})}
          >{index + ': ' + title}</Button>
        )}
      </Selectors>
    );

    return (
      <Wrapper>
        <div>{tabs}</div>
        <Description>{description}</Description>
        <Diff
          // hack to get prism to detect the language
          className="language-lisp"
          hunks={hunks}
          viewType="unified"
          widgets={widgets}
          onRenderCode={elem => Prism.highlightElement(elem)}
        />
      </Wrapper>
    );
  }
}
